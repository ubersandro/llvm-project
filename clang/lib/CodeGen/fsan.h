/** HEADER for FSAN utils */
#ifndef FSAN_H
#define FSAN_H
#include "clang/AST/ParentMapContext.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/IR/InstrTypes.h"
// #include "llvm/Support/Casting.h"

namespace FSAN {

// NOTE: no new operator, that's a different story
inline std::set<std::string> allocFunctions = {"malloc", "realloc", "calloc",
                                               "reallocarray"};
// TODO: handle more!
// "memalign",
// "aligned_alloc", "posix_memalign", "valloc", "pvalloc"};
inline std::set<std::string> fullsetOfAllocFunctions = {
    "malloc",        "realloc",        "calloc", "reallocarray", "memalign",
    "aligned_alloc", "posix_memalign", "valloc", "pvalloc"};

// inline void printExprLocation(const clang::Expr *E, clang::SourceManager &SM) {
//   auto SL = E->getExprLoc();
//   // auto &SM = CGF.getContext().getSourceManager();
//   if (SL.isValid()) {
//     auto P = SM.getPresumedLoc(SL);
//     if (P.isInvalid())
//       P = SM.getPresumedLoc(SM.getSpellingLoc(SL));
//     if (!P.isInvalid())
//       llvm::errs() << "[DBG]:- EXPRESSION DUMP, SRC LOC: " << P.getFilename()
//                    << ":" << P.getLine() << ":" << P.getColumn() << "\n";
//   }
// }

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
  if (const auto *DRE = llvm::dyn_cast<clang::DeclRefExpr>(
          Call->getCallee()->IgnoreParenImpCasts())) {
    if (const auto *FD = llvm::dyn_cast<clang::FunctionDecl>(DRE->getDecl()))
      return matchesAllocFn(FD);
  }

  // Case 3: __builtin_malloc etc.
  // TODO: debug this case eventually
  // if (const auto *CE = llvm::dyn_cast<clang::ImplicitCastExpr>(Call->getCallee()))
  // {
  //   if (const auto *DRE = llvm::dyn_cast<clang::DeclRefExpr>(CE->getSubExpr())) {
  //     if (const auto *FD = llvm::dyn_cast<clang::FunctionDecl>(DRE->getDecl())) {
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

inline bool isAllocFD(const clang::FunctionDecl *FD) {

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

  bool ret = matchesAllocFn(FD);
  return ret;

  // Case 3: __builtin_malloc etc.
  // TODO: debug this case eventually
  // if (const auto *CE = llvm::dyn_cast<clang::ImplicitCastExpr>(Call->getCallee()))
  // {
  //   if (const auto *DRE = llvm::dyn_cast<clang::DeclRefExpr>(CE->getSubExpr())) {
  //     if (const auto *FD = llvm::dyn_cast<clang::FunctionDecl>(DRE->getDecl())) {
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
}

// NOTE: this does not work because you cannot persist ptrs inside global!
inline __attribute__((weak)) void
persistWithSideEffect(clang::CodeGen::CGBuilderTy &Builder,
                      llvm::Value *resultPtr, const std::string &IRTypeName,
                      int64_t ArraySize, clang::CodeGen::CodeGenFunction &CGF,
                      clang::CodeGen::CodeGenModule &CGM) {
  // In EmitCXXNewExpr:
  llvm::Function *SideEffectFn = llvm::Intrinsic::getDeclaration(
      &CGM.getModule(), llvm::Intrinsic::sideeffect);

  std::string TypeStr = IRTypeName + ":" + std::to_string(ArraySize);
  llvm::Constant *TypeStrGlobal =
      Builder.CreateGlobalString(TypeStr, ".fsan.typestr");

  // Emit the sideeffect intrinsic
  llvm::CallInst *SideEffect = Builder.CreateCall(SideEffectFn);

  // Attach metadata carrying all the info
  llvm::MDNode *AllocMD = llvm::MDNode::get(
      CGF.getLLVMContext(),
      {llvm::MDString::get(CGF.getLLVMContext(), "fsan.porcodio"),
       llvm::ValueAsMetadata::get(resultPtr),     // the allocated pointer
       llvm::ValueAsMetadata::get(TypeStrGlobal), // type string global
       llvm::ConstantAsMetadata::get(llvm::ConstantInt::get(
           llvm::Type::getInt64Ty(CGF.getLLVMContext()), ArraySize))});

  SideEffect->setMetadata("fsan.alloc", AllocMD);
}

inline __attribute__((weak)) void persistWithStore(
    clang::CodeGen::CGBuilderTy &Builder, clang::CodeGen::Address resultAddr,
    const std::string &IRTypeName, int64_t ArraySize,
    clang::CodeGen::CodeGenFunction &CGF, clang::CodeGen::CodeGenModule &CGM) {

  // auto String = Builder.CreateGlobalString(IRTypeName + ":" +
  // std::to_string(ArraySize), ".fsan.typestr"); String->setName(IRTypeName +
  // ":" + std::to_string(ArraySize)); Builder.CreateStore(String, resultAddr,
  // /*isVolatile=*/true); llvm::Constant *NullValue =
  // llvm::Constant::getNullValue(resultAddr.getType());
  // NullValue->setName(IRTypeName + ":" + std::to_string(ArraySize));
  // llvm::Constant *setToZero =
  // llvm::ConstantInt::get(llvm::Type::getInt64Ty(CGF.getLLVMContext()), 0);
  // setToZero->setName(IRTypeName + ":" + std::to_string(ArraySize));
  // Builder.CreateStore(setToZero, resultAddr, /*isVolatile=*/true);
  {
    // llvm::LLVMContext &Ctx = CGF.getLLVMContext();
    // llvm::Type *I8Ty = llvm::Type::getInt8Ty(Ctx);
    // // bitcast the address pointer to i8*
    // llvm::Value *BytePtr =
    //     Builder.CreateBitCast(resultAddr.getPointer(), I8Ty->getPointerTo());
    // // load a single byte and name the load with IRTypeName
    Builder.CreateLoad(resultAddr, true, IRTypeName);
  }
}

inline __attribute__((weak)) void
persistInGlobalVar(clang::CodeGen::CGBuilderTy &Builder, llvm::Value *resultPtr,
                   const std::string &IRTypeName, int64_t ArraySize,
                   clang::CodeGen::CodeGenFunction &CGF,
                   clang::CodeGen::CodeGenModule &CGM) {
  // In EmitCXXNewExpr after getting the allocation pointer:

  llvm::Module &M = CGM.getModule();
  llvm::LLVMContext &Ctx = CGF.getLLVMContext();

  // Get or create the global registry array
  // This is a global that holds [ptr, type_string_ptr, size] tuples

  /** ONE  ERRORL Global is external, but doesn't have external or weak linkage!
ptr @__fsan_alloc_registry  */

  llvm::GlobalVariable *Registry =
      M.getGlobalVariable("__fsan_alloc_registry", true);

  if (!Registry) {
    // Create array type: { ptr, ptr, i64 }
    llvm::StructType *EntryTy = llvm::StructType::create(
        Ctx,
        {
            llvm::PointerType::getUnqual(Ctx), // allocated pointer
            llvm::PointerType::getUnqual(Ctx), // type string
            llvm::Type::getInt64Ty(Ctx)        // array size
        },
        "fsan_alloc_entry");

    llvm::ArrayType *RegistryTy = llvm::ArrayType::get(EntryTy, 1); // unsized

    Registry = new llvm::GlobalVariable(
        M, RegistryTy, false, llvm::GlobalValue::InternalLinkage,
        llvm::Constant::getNullValue(RegistryTy), "__fsan_alloc_registry");
  }

  // Create the type string as a global constant
  std::string TypeStr = IRTypeName + ":" + std::to_string(ArraySize);
  llvm::Constant *TypeStrGlobal =
      Builder.CreateGlobalString(TypeStr, ".fsan.typestr");

  // Build the entry struct: { resultPtr, TypeStrGlobal, ArraySize }
  llvm::Value *Entry = llvm::UndefValue::get(llvm::StructType::get(
      Ctx, {resultPtr->getType(), TypeStrGlobal->getType(),
            llvm::Type::getInt64Ty(Ctx)}));

  Entry = Builder.CreateInsertValue(Entry, resultPtr, 0);
  Entry = Builder.CreateInsertValue(Entry, TypeStrGlobal, 1);
  Entry = Builder.CreateInsertValue(
      Entry, llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), ArraySize), 2);

  clang::CodeGen::Address Addr = clang::CodeGen::Address(
      Registry, Registry->getType(), clang::CharUnits::fromQuantity(8));
  Builder.CreateStore(Entry, Addr, /*isVolatile=*/true);
  // Volatile store = guaranteed not to be eliminated
}
/**
EmitDeclStmt
VisitBinAssign
TODO: double check on sizeof with N arguments, N>2
 */
inline __attribute__((weak)) void
TagFromBitcast(llvm::Value *Src, clang::QualType DestTy,
               clang::CodeGen::CodeGenFunction &CGF) {
  llvm::Type *SrcTy = Src->getType();

  if (DestTy->isPointerType()) {
    if (auto *Call = llvm::dyn_cast<llvm::CallBase>(Src)) {
      if (llvm::CallBase *CI = llvm::dyn_cast<llvm::CallBase>(Call)) {

        llvm::Function *Callee = llvm::dyn_cast<llvm::Function>(
            CI->getCalledOperand()->stripPointerCasts());
        // if (!Callee) {
        //   llvm::Value *V = CI->getCalledOperand()->stripPointerCasts();
        //   Callee = llvm::dyn_cast<llvm::Function>(V);
        if (Callee && Callee->getName() == "typed_allocation") {

          // CI->dump();
          auto nArgs = CI->arg_size();
          auto typeStrArgIdx = nArgs - 3; // NOT THERE YET
          auto typeStr = CI->getArgOperand(typeStrArgIdx);

          llvm::errs() << "TagFromBitcast: SRC: " << *Src
                       << " -  DestTy: " << DestTy << "\n";
          // typeStr->dump();
          std::string typeStrToStr;
          if (llvm::Constant *name = llvm::dyn_cast<llvm::Constant>(typeStr)) {
            if (llvm::ConstantDataArray *dataArray =
                    llvm::dyn_cast<llvm::ConstantDataArray>(name->getOperand(0))) {
              if (dataArray->isString()) {
                // llvm::errs() << "\t\tTYPE STR: "
                //              << dataArray->getAsString() << "\n";
                typeStrToStr = dataArray->getAsString().str().substr(
                    0, dataArray->getAsString().size() - 1);
              }
            }
          }

          if (typeStrToStr == "PLACEHOLDER") {

            clang::QualType PointeeTy = DestTy->getPointeeType();
            llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
            std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                          ? IRPointeeTy->getStructName().str()
                                          : "scalar";
            // TODO: literal structs should be "scalar" -> CHECK
            llvm::errs() << "- REPLACE PLACEHOLDER: " << typeStrToStr << " ->  "
                         << IRTyNameStr << "\n";
            llvm::StringRef IRPointeeTyName(IRTyNameStr);
            // CI->replaceArgWith(typeStrArgIdx,
            // CGF.Builder.CreateGlobalString(IRPointeeTyName)); // this method
            // is BS, does not exist
            llvm::Value *NewTypeStr =
                CGF.Builder.CreateGlobalString(IRPointeeTyName);
            CI->setArgOperand(typeStrArgIdx, NewTypeStr);
            llvm::errs() << "Updated call instruction: ";
            // CI->dump();
          } //
        }
        // }
      }

      return;
      // STOP HERE, we dont care about metadata

      auto *Callee = Call->getCalledOperand()->stripPointerCasts();
      if (Callee) {
        auto name = Callee->getName();
        if (allocFunctions.find(name.str()) != allocFunctions.end()) {
          clang::QualType PointeeTy = DestTy->getPointeeType();
          llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
          std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                        ? IRPointeeTy->getStructName().str()
                                        : "scalar";
          // TODO: literal structs should be "scalar" -> CHECK
          llvm::StringRef IRPointeeTyName(IRTyNameStr);
          // llvm::errs() << "\t\tBITCAST: SRC: " << *SrcTy << " -  DestTy: ";
          // llvm::errs() << IRPointeeTyName << "\n";
          // Call->dump();
          // also print the src location where this happens
          // llvm::errs() << "\t\t\tBITCAST: Allocation site: ";
          // Try to use LLVM debug location attached to the call instruction.
          // if (auto *Inst = llvm::dyn_cast<llvm::Instruction>(Call)) {
          //   if (auto DL = Inst->getDebugLoc()) {
          //     if (auto *Loc = DL.get()) {
          //       llvm::errs() << Loc->getFilename() << ":" << Loc->getLine()
          //                    << ":" << Loc->getColumn();
          //     } else {
          //       llvm::errs() << "unknown-location";
          //     }
          //   } else {
          //     llvm::errs() << "no-debug-location";
          //   }
          // } else {
          //   llvm::errs() << "non-instruction-value";
          // }

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
            // llvm::errs() << "BITCAST HANDLER: ALREADY HAS MD! ";
            // Call->getMetadata("fsan.alloc")->dump();
            // TODO: if MD type is "porcodiotype", set correct type
            auto MDNode = Call->getMetadata("fsan.alloc");
            auto *MDS = llvm::dyn_cast<llvm::MDString>(MDNode->getOperand(1));
            std::string TypeStrMD =
                MDS ? MDS->getString().str() : std::string();
            if (TypeStrMD == "porcodiotype") {
              Call->setMetadata("fsan.alloc", FSanMD);
              // llvm::errs() << "BITCAST HANDLER: UPDATING MD! ";
              // Call->getMetadata("fsan.alloc")->dump();
              // Call->dump();
              // rewrite the type arg of the call
            }

          } else {
            llvm::errs() << "BITCAST HANDLER: SETTING MD! ";
            Call->setMetadata("fsan.alloc", FSanMD);
            // FSanMD->dump();
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

// inline void dumpAllocSite(const clang::CallExpr *E, llvm::StringRef FNName,
//                           clang::CodeGen::CodeGenFunction &CGF) {
//   llvm::errs() << "(FE)ALLOCATION SITE: "
//                << E->getExprLoc().printToString(
//                       CGF.getContext().getSourceManager())
//                << ", FUNCTION: " << FNName << "\n";
// }

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

/** Parses sizeof and assignment data. */
inline void TagFromCallSite(const clang::CallExpr *E,
                            clang::CodeGen::CodeGenFunction &CGF,
                            clang::CodeGen::RValue Call,
                            clang::CodeGen::CGCallee Callee) {
  auto FNName = Callee.getFunctionPointer()->getName();

  // reset pending type
  if (CGF.PendingTypeIsValid) {
    CGF.FSanPendingAllocType = clang::QualType();
    CGF.PendingTypeIsValid = false;
  }

  if (FSAN::allocFunctions.count(FNName.str())) {
    // dumpAllocSite(E, FNName, CGF);
    auto ArraySize = -1;
    for (const auto *Arg : E->arguments()) {
      if (auto *unaryOperatorArg =
              llvm::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(Arg)) {
        if (unaryOperatorArg->getKind() == clang::UETT_SizeOf) {
          // when the call has 1 sizeof arg, array size is 1
          clang::QualType TypeToSize = unaryOperatorArg->getTypeOfArgument();
          TypeToSize = CGF.getContext().getCanonicalType(TypeToSize);
          // llvm::errs() << "TagFromCallSite: SIZEOF : "
          //              << TypeToSize.getAsString() << ", SRC LOC: "
          //              << Arg->getExprLoc().printToString(
          //                     CGF.getContext().getSourceManager())
          //              << "\n";
          clang::QualType PointeeTy = TypeToSize;
          llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
          std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                        ? IRPointeeTy->getStructName().str()
                                        : "scalar";
          llvm::StringRef IRPointeeTyName(IRTyNameStr);
          CGF.FSanPendingAllocType = TypeToSize;
          CGF.PendingTypeIsValid = true;
          // llvm::errs()
          //     << "[DBG-FSAN] This is a sizeof operator in the argument! Type: "
          //     << TypeToSize.getAsString() << "\n";

          if (auto *Instr = llvm::dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
            ArraySize = 1;
            llvm::MDNode *FSanMD =
                createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
            Instr->setMetadata("fsan.alloc", FSanMD);
            // llvm::errs()
            //     << "\t\t[DBG-FSAN] fsan metadata attached to instruction:\t\t";
            // Instr->dump();
            // llvm::errs() << "\n";
          }
        }
      } else if (auto *binaryoperator = llvm::dyn_cast<clang::BinaryOperator>(Arg)) {
        if (binaryoperator->getOpcode() == clang::BO_Mul) {
          if (auto *RHS = llvm::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(
                  binaryoperator->getRHS())) {
            if (RHS->getKind() == clang::UETT_SizeOf) {
              clang::QualType TypeToSize = RHS->getTypeOfArgument();
              // llvm::errs()
              //     << "RHS: This is a sizeof operator in the argument! Type: "
              //     << TypeToSize.getAsString() << ", SRC LOC: "
              //     << RHS->getExprLoc().printToString(
              //            CGF.getContext().getSourceManager())
              //     << "\n";

              //   llvm::LLVMContext &LLVMCtx = CGF.getLLVMContext();
              clang::QualType PointeeTy = TypeToSize;
              llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
              std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                            ? IRPointeeTy->getStructName().str()
                                            : "scalar";
              llvm::StringRef IRPointeeTyName(IRTyNameStr);
              CGF.FSanPendingAllocType = TypeToSize;
              CGF.PendingTypeIsValid = true;
              // NOTE: we dont care about array size here
              if (auto *Instr =
                      llvm::dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
                llvm::MDNode *FSanMD =
                    createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
                // must be an instr. TODO: check if this is the case.
                Instr->setMetadata("fsan.alloc", FSanMD);
                // llvm::errs() << "\t\t[DBG-FSAN] fsan metadata attached to "
                //                 "instruction:\t\t";
                // Instr->dump();
                // llvm::errs() << "\n";
              }
            }

          } else if (auto *LHS = llvm::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(
                         binaryoperator->getLHS())) {
            if (LHS->getKind() == clang::UETT_SizeOf) {
              clang::QualType TypeToSize = LHS->getTypeOfArgument();
              // llvm::errs()
              //     << "LHS: This is a sizeof operator in the argument! Type: "
              //     << TypeToSize.getAsString() << ", SRC LOC: "
              //     << LHS->getExprLoc().printToString(
              //            CGF.getContext().getSourceManager())
              //     << "\n";

              //   llvm::LLVMContext &LLVMCtx = CGF.getLLVMContext();
              clang::QualType PointeeTy = TypeToSize;
              llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
              std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                            ? IRPointeeTy->getStructName().str()
                                            : "scalar";
              llvm::StringRef IRPointeeTyName(IRTyNameStr);
              CGF.FSanPendingAllocType = TypeToSize;
              CGF.PendingTypeIsValid = true;
              if (auto *Instr =
                      llvm::dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
                // must be an instr. TODO: check if this is the case.
                llvm::MDNode *FSanMD =
                    createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
                Instr->setMetadata("fsan.alloc", FSanMD);
                // llvm::errs() << "\t\t[DBG-FSAN] fsan metadata attached to "
                //                 "instruction:\t\t";
                // Instr->dump();
                // llvm::errs() << "\n";
              }

            } // LHS is sizeof
          }
        }
      }
    } // for arguments

    auto info = FSAN::extractAssignment(E, CGF.getContext());
    if (info) {
      // llvm::errs() << "\t\t[FrontEnd] ASSIGNEE TYPE: "
      //              << info->LHSType.getAsString()
      //              << " POINTEE TYPE: " << info->PointeeType.getAsString()
      //              << " IS DECLARATION: " << info->IsDeclaration << "\n";

      if (Call.isScalar()) {
        // Call.getScalarVal()->dump();
        clang::QualType PointeeTy = info->PointeeType;
        llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
        std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                      ? IRPointeeTy->getStructName().str()
                                      : "scalar";
        // must match the one used for the Lookup
        llvm::StringRef IRPointeeTyName(IRTyNameStr);
        // bool isVoidPtr = info->LHSType->isVoidPointerType();

        if (!CGF.PendingTypeIsValid) {
          CGF.FSanPendingAllocType = PointeeTy;
          CGF.PendingTypeIsValid = true;
        }

        // else return; // you are done if you found it

        // if (auto *Instr = llvm::dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
        //   // must be an instr. TODO: check if this is the case.
        //   llvm::MDNode *FSanMD =
        //       createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
        //   Instr->setMetadata("fsan.alloc", FSanMD);
        //   llvm::errs() << "\t\tMetadata attached to instruction:\n";
        //   Instr->dump();
        //   llvm::errs() << "\n";
        // }
        // LLM BS
      } // if Call is scalar

      // else if (Call.isComplex()) {
      //   llvm::errs() << "TODO: handle Complex value:\n";
      //   // Call.getComplexVal().first->dump();
      //   // Call.getComplexVal().second->dump();
      // } else if (Call.isAggregate()) {
      //   llvm::errs() << "TODO: handle Aggregate at address: ";
      //   // TODO: for later
      //   // Call.getAggregateAddress()
      // } else
      //   llvm::errs() << "\t\t[FrontEnd] NO ASSIGNEE TYPE FOUND\n";
    } // if info
    else {
      // NO ASSIGNMENT INFO AVAILABLE
      // NOTE: it can happen not to find any sizeof or assignment information at
      // this time,  bail out in such a case
      std::string dummyPorcodio = "porcodiotype";
      std::string IRTyNameStr = "";
      /**
      std::string IRTyNameStr = IRPointeeTy->isStructTy()
                                      ? IRPointeeTy->getStructName().str()
                                      : "scalar"; */
      if (!CGF.PendingTypeIsValid) {
        // llvm::errs() << "\t\t[FrontEnd - TagFromCallSite] NoAss and no SizeOf: "
        //                 "putting dummmy str for type str\n";
        // // DONT BAIL OUT HERE, put guard value that tells next steps to
        // // intervene
        // llvm::errs() << "\t\t\tAllocation site: "
        //              << E->getExprLoc().printToString(
        //                     CGF.getContext().getSourceManager())
        //              << ", in function: " << FNName << "\n";
        IRTyNameStr = dummyPorcodio;
      } // if no pending type
      else {
        // TYPE IS VALID
        clang::QualType PendingTy = CGF.FSanPendingAllocType;
        if (!PendingTy.isNull()) {
          // llvm::errs() << "\t\t[FrontEnd] Applying pending type: "
          //              << PendingTy.getAsString() << "\n";
          clang::QualType PointeeTy;
          if (PendingTy->isPointerType())
            PointeeTy = PendingTy->getPointeeType();
          else
            PointeeTy = PendingTy;

          llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
          // llvm::errs() << "\t\t[FrontEnd] Applying pending type, IR type: "
          //              << *IRPointeeTy << "\n";
          IRTyNameStr = IRPointeeTy->isStructTy()
                            ? IRPointeeTy->getStructName().str()
                            : "scalar";
        } // pending type is !null
      } // pending type is valid
      // at this point, that type could be null? TODO: check later

      llvm::StringRef IRPointeeTyName(IRTyNameStr);
      ArraySize = -1;
      if (auto *Instr = llvm::dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
        // must be an instr. TODO: check if this is the case.
        llvm::MDNode *FSanMD =
            createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
        Instr->setMetadata("fsan.alloc", FSanMD);
        // llvm::errs() << "\t\tMetadata attached to instruction:\n";
        // Instr->dump();
        // llvm::errs() << "\n";
      } // if instr

    } // when no assignment info
  } // if function is allocation
} // tagFromCallSite

// TODO: tag from assignment side?

} // namespace FSAN
#endif
