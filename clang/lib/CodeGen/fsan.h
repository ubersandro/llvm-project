/** HEADER for FSAN utils */
#ifndef FSAN_H
#define FSAN_H
#include "clang/AST/ParentMapContext.h"
#include "clang/Basic/SourceManager.h"

namespace FSAN {

inline std::set<std::string> allocFunctions = {
    "malloc",        "realloc",        "calloc", "reallocarray", "memalign",
    "aligned_alloc", "posix_memalign", "valloc", "pvalloc"};

inline void printExprLocation(const clang::Expr *E, clang::SourceManager &SM) {
  auto SL = E->getExprLoc();
  // auto &SM = CGF.getContext().getSourceManager();
  if (SL.isValid()) {
    auto P = SM.getPresumedLoc(SL);
    if (P.isInvalid())
      P = SM.getPresumedLoc(SM.getSpellingLoc(SL));
    if (!P.isInvalid())
      llvm::errs() << "[DBG]:- EXPRESSION DUMP, SRC LOC: " << P.getFilename()
                   << ":" << P.getLine() << ":" << P.getColumn() << "\n";
  }
}

inline bool isAllocCall(const clang::CallExpr *Call) {
  if (!Call)
    return false;

  auto matchesAllocFn = [](const clang::FunctionDecl *FD) -> bool {
    if (!FD)
      return false;
    // getIdentifier() returns null for operator overloads, destructors,
    // conversion functions etc. -- bail out early for those.
    const clang::IdentifierInfo *II = FD->getIdentifier();
    if (!II)
      return false;
    return allocFunctions.count(II->getName().str()) > 0;
  };

  // Case 1: direct call
  if (const auto *FD = Call->getDirectCallee())
    return matchesAllocFn(FD);

  // Case 2: macro-wrapped call
  if (const auto *DRE = dyn_cast<clang::DeclRefExpr>(
          Call->getCallee()->IgnoreParenImpCasts())) {
    if (const auto *FD = dyn_cast<clang::FunctionDecl>(DRE->getDecl()))
      return matchesAllocFn(FD);
  }

  // Case 3: __builtin_malloc etc.
  // TODO: debug this case eventually
  // if (const auto *CE = dyn_cast<clang::ImplicitCastExpr>(Call->getCallee()))
  // {
  //   if (const auto *DRE = dyn_cast<clang::DeclRefExpr>(CE->getSubExpr())) {
  //     if (const auto *FD = dyn_cast<clang::FunctionDecl>(DRE->getDecl())) {
  //       const clang::IdentifierInfo *II = FD->getIdentifier();
  //       if (!II)
  //         return false;
  //       llvm::StringRef Name = II->getName();
  //       // Strip __builtin_ prefix then check
  //       Name.consume_front("__builtin_");
  //       return allocFunctions.count(Name.str()) > 0;
  //     }
  //   }
  // }

  return false;
}

inline __attribute__((weak)) void
TagFromBitcast(llvm::Value *Src, clang::QualType DestTy,
               clang::CodeGen::CodeGenFunction &CGF) {

  llvm::Type *SrcTy = Src->getType();

  if (DestTy->isPointerType()) {
    if (auto *Call = dyn_cast<llvm::CallBase>(Src)) {
      auto *Callee = Call->getCalledOperand()->stripPointerCasts();
      if (Callee) { // && isa<llvm::Function>(Callee)
        auto name = Callee->getName();
        if (allocFunctions.find(name.str()) != allocFunctions.end()) {
          clang::QualType PointeeTy = DestTy->getPointeeType();
          llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
          std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                        ? IRPointeeTy->getStructName().str()
                                        : "scalar";
          // TODO: literal structs should be "scalar" -> CHECK
          llvm::StringRef IRPointeeTyName(IRTyNameStr);
          llvm::errs() << "\t\tBITCAST: SRC: " << *SrcTy << " -  DestTy: ";
          llvm::errs() << IRPointeeTyName << "\n";
          Call->dump();

          auto ArraySize = -1;

          llvm::LLVMContext &LLVMCtx = CGF.getLLVMContext();
          llvm::MDNode *FSanMD = llvm::MDNode::get(
              LLVMCtx, {
                           llvm::MDString::get(LLVMCtx, "fsan.alloc"),
                           llvm::MDString::get(LLVMCtx, IRPointeeTyName),
                           llvm::ValueAsMetadata::get(llvm::ConstantInt::get(
                               llvm::Type::getInt64Ty(LLVMCtx), ArraySize)),
                       });

          // NOTE: bitcast operator -> cannot infer size, if the MD node is
          // there, I trust it to have the size OW I try and give info about
          // the type, at least.
          if (Call->getMetadata("fsan.alloc")) {
            llvm::errs() << "BITCAST HANDLER: ALREADY HAS MD! ";
            Call->getMetadata("fsan.alloc")->dump();
          } else {
            llvm::errs() << "BITCAST HANDLER: SETTING MD! ";
            Call->setMetadata("fsan.alloc", FSanMD);
            FSanMD->dump();
          }
        } // allocation function

      } // Callee && isa<llvm::Function>
    } // Call
  } // Dst is pointer type
}

struct AssignmentInfo {
  clang::QualType LHSType;     // type of the LHS variable
  clang::QualType PointeeType; // dereferenced, if pointer
  bool IsDeclaration;          // true if this is T* p = malloc(n)
};

inline std::optional<AssignmentInfo>
extractAssignment(const clang::CallExpr *Call, clang::ASTContext &Ctx) {
  // Walk up: CallExpr -> (ImplicitCast?) -> (BinaryOperator | VarDecl)
  //   auto Parents = Ctx.getParents(*Call);
  auto Parents = Ctx.getParentMapContext().getParents(*Call->IgnoreImpCasts());
  // NOTE: THIS IS PARTIAL -> you cannot assume that the parent exists, this
  // might be an expression that has no parent (yet). Working at call level is
  // incomplete!

  while (!Parents.empty()) {
    llvm::errs() << "Parent: " << Parents[0].getNodeKind().asStringRef()
                 << "\n";
    if (Parents[0].get<clang::ImplicitCastExpr>() ||
        Parents[0].get<clang::CStyleCastExpr>()) {
      const clang::Expr *E = Parents[0].get<clang::Expr>();
      Parents = Ctx.getParents(*E);
      continue;
    }
    break;
  }
  if (Parents.empty()) {
    // TODO: this is TOO frequent, because of how code is parsed. Implement same
    // at ASS time.
    llvm::errs() << "\t\t\tNo valid parent found for allocation\n";
    return std::nullopt;
  }

  // NOTE: you wanna recover ALL types and then add annotations only for those
  // of Case 1: p = malloc(n)  →  BinaryOperator(BO_Assign)
  if (const auto *BO = Parents[0].get<clang::BinaryOperator>()) {
    if (BO->getOpcode() != clang::BO_Assign)
      return std::nullopt;
    clang::QualType LT = BO->getLHS()->getType();
    if (!LT->isPointerType())
      return std::nullopt;

    clang::QualType Pointee = LT->getPointeeType();
    return AssignmentInfo{LT, Pointee, false};
  }

  // Case 2: T* p = malloc(n)  →  VarDecl with initializer
  if (const auto *VD = Parents[0].get<clang::VarDecl>()) {
    clang::QualType LT = VD->getType();
    if (!LT->isPointerType())
      return std::nullopt;
    clang::QualType Pointee = LT->getPointeeType();
    return AssignmentInfo{LT, Pointee, true};
  }

  return std::nullopt;
}

inline void dumpAllocSite(const clang::CallExpr *E, llvm::StringRef FNName,
                          clang::CodeGen::CodeGenFunction &CGF) {
  llvm::errs() << "(FE)ALLOCATION SITE: "
               << E->getExprLoc().printToString(
                      CGF.getContext().getSourceManager())
               << ", FUNCTION: " << FNName << "\n";
}

inline llvm::MDNode *createFSanMD(std::string TyName, int64_t ArraySize,
                                  clang::CodeGen::CodeGenFunction &CGF) {
  llvm::LLVMContext &LLVMCtx = CGF.getLLVMContext();
  llvm::MDNode *FSanMD = llvm::MDNode::get(
      LLVMCtx, {
                   llvm::MDString::get(LLVMCtx, "fsan.alloc"),
                   llvm::MDString::get(LLVMCtx, TyName),
                   llvm::ValueAsMetadata::get(llvm::ConstantInt::get(
                       llvm::Type::getInt64Ty(LLVMCtx), ArraySize)),
               });
  return FSanMD;
}

inline void TagFromCallSite(const clang::CallExpr *E,
                            clang::CodeGen::CodeGenFunction &CGF,
                            clang::CodeGen::RValue Call,
                            clang::CodeGen::CGCallee Callee) {
  auto FNName = Callee.getFunctionPointer()->getName();
  if (FSAN::allocFunctions.count(FNName.str())) {
    dumpAllocSite(E, FNName, CGF);
    auto ArraySize = -1;
    for (const auto *Arg : E->arguments()) {

      if (auto *unaryOperatorArg =
              dyn_cast<clang::UnaryExprOrTypeTraitExpr>(Arg)) {
        if (unaryOperatorArg->getKind() == clang::UETT_SizeOf) {
          // when the call has 1 sizeof arg, array size is 1
          clang::QualType TypeToSize = unaryOperatorArg->getTypeOfArgument();
          TypeToSize = CGF.getContext().getCanonicalType(TypeToSize);
          clang::QualType PointeeTy = TypeToSize;
          llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
          std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                        ? IRPointeeTy->getStructName().str()
                                        : "scalar";
          llvm::StringRef IRPointeeTyName(IRTyNameStr);

          if (auto *Instr = dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
            ArraySize = 1;
            llvm::MDNode *FSanMD =
                createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
            Instr->setMetadata("fsan.alloc", FSanMD);
            llvm::errs()
                << "\t\t[DBG-FSAN] fsan metadata attached to instruction:\t\t";
            Instr->dump();
            llvm::errs() << "\n";
          }
        }
      } else if (auto *binaryoperator = dyn_cast<clang::BinaryOperator>(Arg)) {
        if (binaryoperator->getOpcode() == clang::BO_Mul) {
          if (auto *RHS = dyn_cast<clang::UnaryExprOrTypeTraitExpr>(
                  binaryoperator->getRHS())) {
            if (RHS->getKind() == clang::UETT_SizeOf) {
              clang::QualType TypeToSize = RHS->getTypeOfArgument();
              llvm::errs()
                  << "RHS: This is a sizeof operator in the argument! Type: "
                  << TypeToSize.getAsString() << "\n";

              //   llvm::LLVMContext &LLVMCtx = CGF.getLLVMContext();
              clang::QualType PointeeTy = TypeToSize;
              llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
              std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                            ? IRPointeeTy->getStructName().str()
                                            : "scalar";
              llvm::StringRef IRPointeeTyName(IRTyNameStr);

              if (auto *Instr =
                      dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
                llvm::MDNode *FSanMD =
                    createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
                // must be an instr. TODO: check if this is the case.
                Instr->setMetadata("fsan.alloc", FSanMD);
                llvm::errs() << "\t\t[DBG-FSAN] fsan metadata attached to "
                                "instruction:\t\t";
                Instr->dump();
                llvm::errs() << "\n";
              }
            }

          } else if (auto *LHS = dyn_cast<clang::UnaryExprOrTypeTraitExpr>(
                         binaryoperator->getLHS())) {
            if (LHS->getKind() == clang::UETT_SizeOf) {
              clang::QualType TypeToSize = LHS->getTypeOfArgument();
              llvm::errs()
                  << "LHS: This is a sizeof operator in the argument! Type: "
                  << TypeToSize.getAsString() << "\n";

              //   llvm::LLVMContext &LLVMCtx = CGF.getLLVMContext();
              clang::QualType PointeeTy = TypeToSize;
              llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
              std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                            ? IRPointeeTy->getStructName().str()
                                            : "scalar";
              llvm::StringRef IRPointeeTyName(IRTyNameStr);

              if (auto *Instr =
                      dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
                // must be an instr. TODO: check if this is the case.
                llvm::MDNode *FSanMD =
                    createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
                Instr->setMetadata("fsan.alloc", FSanMD);
                llvm::errs() << "\t\t[DBG-FSAN] fsan metadata attached to "
                                "instruction:\t\t";
                Instr->dump();
                llvm::errs() << "\n";
              }

            } // LHS is sizeof
          }
        }
      }
    } // for arguments

    auto info = FSAN::extractAssignment(E, CGF.getContext());
    if (info) {
      llvm::errs() << "\t\t[FrontEnd] ASSIGNEE TYPE: "
                   << info->LHSType.getAsString()
                   << " POINTEE TYPE: " << info->PointeeType.getAsString()
                   << " IS DECLARATION: " << info->IsDeclaration << "\n";

      if (Call.isScalar()) {
        Call.getScalarVal()->dump();
        // llvm::LLVMContext &LLVMCtx = CGF.getLLVMContext();

        clang::QualType PointeeTy = info->PointeeType;
        llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
        std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                      ? IRPointeeTy->getStructName().str()
                                      : "scalar";
        // must match the one used for the Lookup
        llvm::StringRef IRPointeeTyName(IRTyNameStr);

        if (auto *Instr = dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
          // must be an instr. TODO: check if this is the case.
          llvm::MDNode *FSanMD =
              createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
          Instr->setMetadata("fsan.alloc", FSanMD);
          llvm::errs() << "\t\tMetadata attached to instruction:\n";
          Instr->dump();
          llvm::errs() << "\n";
        }
        // LLM BS
      } // if Call is scalar

      else if (Call.isComplex()) {
        llvm::errs() << "TODO: handle Complex value:\n";
        // Call.getComplexVal().first->dump();
        // Call.getComplexVal().second->dump();
      } else if (Call.isAggregate()) {
        llvm::errs() << "TODO: handle Aggregate at address: ";
        // TODO: for later
        // Call.getAggregateAddress()
      } else
        llvm::errs() << "\t\t[FrontEnd] NO ASSIGNEE TYPE FOUND\n";
    } // if info
    else {
      // apply pending type
      clang::QualType PendingTy = CGF.FSanPendingAllocType;
      if (!PendingTy.isNull()) {
        llvm::errs() << "\t\t[FrontEnd] Applying pending type: "
                     << PendingTy.getAsString() << "\n";
        clang::QualType PointeeTy = PendingTy->getPointeeType();
        llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
        std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                      ? IRPointeeTy->getStructName().str()
                                      : "scalar";
        llvm::StringRef IRPointeeTyName(IRTyNameStr);
        ArraySize = -1;
        if (auto *Instr = dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
          // must be an instr. TODO: check if this is the case.
          llvm::MDNode *FSanMD =
              createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
          Instr->setMetadata("fsan.alloc", FSanMD);
          llvm::errs() << "\t\tMetadata attached to instruction:\n";
          Instr->dump();
          llvm::errs() << "\n";
        }
      }
    }
  } // if function is allocation
} // tagFromCallSite

// TODO: tag from assignment side?

} // namespace FSAN
#endif
