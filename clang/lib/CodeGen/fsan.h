/** HEADER for FSAN utils */
#ifndef FSAN_H
#define FSAN_H
#include "clang/AST/ParentMapContext.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Constants.h"

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
  // if (const auto *CE =
  // llvm::dyn_cast<clang::ImplicitCastExpr>(Call->getCallee()))
  // {
  //   if (const auto *DRE =
  //   llvm::dyn_cast<clang::DeclRefExpr>(CE->getSubExpr())) {
  //     if (const auto *FD =
  //     llvm::dyn_cast<clang::FunctionDecl>(DRE->getDecl())) {
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
  // if (const auto *CE =
  // llvm::dyn_cast<clang::ImplicitCastExpr>(Call->getCallee()))
  // {
  //   if (const auto *DRE =
  //   llvm::dyn_cast<clang::DeclRefExpr>(CE->getSubExpr())) {
  //     if (const auto *FD =
  //     llvm::dyn_cast<clang::FunctionDecl>(DRE->getDecl())) {
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

inline llvm::Value *
GetArraySizeFromAlloc(const clang::Expr *E,
                      clang::CodeGen::CodeGenFunction &CGF) {
  auto *CallExpr = llvm::dyn_cast<clang::CallExpr>(E);
  const auto *const FunctionDecl = CallExpr->getDirectCallee();
  auto AllocFnName = FunctionDecl->getIdentifier()->getName().str();
  llvm::Value *RET = llvm::ConstantInt::get(llvm::Type::getInt64Ty(CGF.getLLVMContext()), -1);

  llvm::errs() << "[FSAN-FE] GetArraySizeFromAlloc: AllocFnName: "
               << AllocFnName << "\n";
  
  if (AllocFnName == "malloc" || AllocFnName == "valloc" ||
      AllocFnName == "pvalloc") {
    // CASE 0 - malloc(sizeof(something))
    // CASE 1 - malloc(sizeof(something) + flexible array size)
    // CASE 2 - malloc(n * sizeof(something))
    auto *AllocSizeExpr = CallExpr->getArg(0);
    clang::SourceLocation Loc;
    if (auto *BinOp = llvm::dyn_cast<clang::BinaryOperator>(AllocSizeExpr)) {
      Loc = BinOp->getExprLoc();
      if (Loc.isValid()) {
        clang::SourceManager &SM = CGF.getContext().getSourceManager();
        llvm::errs() << "\tSRC: " << SM.getFilename(Loc) << ":"
                     << SM.getSpellingLineNumber(Loc) << "\n";
      }
      clang::Expr* SizeofExpr;
      auto OpCode = BinOp->getOpcode();
      switch (OpCode) {
      case clang::BO_Add:
        llvm::errs() << "[FSAN-FE] DBG ADD OP:\n";
        BinOp->dump();
        RET = llvm::ConstantInt::get(llvm::Type::getInt64Ty(CGF.getLLVMContext()), 1);
        break;

      case clang::BO_Mul:
        llvm::errs() << "[FSAN-FE] DBG MUL OP:\n";
        BinOp->dump();
        // get the sizeof, if any
        SizeofExpr = nullptr;
        SizeofExpr =
            clang::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(BinOp->getLHS());

        if (!SizeofExpr) {
          SizeofExpr =
              clang::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(BinOp->getRHS());
          if (!SizeofExpr) {
            llvm::errs() << "[FSAN-FE] CORNER CASE: no sizeof\n";
          } else {
            // RET is the LHS
            // TODO
          }
        }

        
        break;

      default:
        llvm::errs() << "[FSAN-FE] UNHANDLE OP " << OpCode << "\n";
        BinOp->dump();
        assert(false && "Unhandled binary operator in malloc size expression");
      }
    }
  } // malloc, valloc, pvalloc
  // TODO: calloc
  // TODO: realloc, reallocarray?

  return RET; 
}

inline __attribute__((weak)) void
TagFromBitcast(llvm::Value *Src, clang::QualType DestTy,
               clang::CodeGen::CodeGenFunction &CGF) {
  llvm::Type *SrcTy = Src->getType();

  if (DestTy->isPointerType()) {
    if (auto *Call = llvm::dyn_cast<llvm::CallBase>(Src)) {
      if (llvm::CallBase *CI = llvm::dyn_cast<llvm::CallBase>(Call)) {

        llvm::Function *Callee = llvm::dyn_cast<llvm::Function>(
            CI->getCalledOperand()->stripPointerCasts());
        if (Callee && Callee->getName() == "typed_allocation") {
          auto nArgs = CI->arg_size();
          auto typeStrArgIdx = nArgs - 3; // NOT THERE YET
          auto typeStr = CI->getArgOperand(typeStrArgIdx);
          std::string typeStrToStr;
          if (llvm::Constant *name = llvm::dyn_cast<llvm::Constant>(typeStr)) {
            llvm::ConstantDataArray *dataArray =
                llvm::dyn_cast<llvm::ConstantDataArray>(name->getOperand(0));
            if (dataArray) {
              if (dataArray->isString()) {
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
            llvm::StringRef IRPointeeTyName(IRTyNameStr);
            llvm::Value *NewTypeStr =
                CGF.Builder.CreateGlobalString(IRPointeeTyName);
            CI->setArgOperand(typeStrArgIdx, NewTypeStr);
          }
        }
      }
    }
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
    // llvm::errs() << "Parent: " << Parents[0].getNodeKind().asStringRef()
    //              << "\n";
    if (Parents[0].get<clang::ImplicitCastExpr>() ||
        Parents[0].get<clang::CStyleCastExpr>()) {
      const clang::Expr *E = Parents[0].get<clang::Expr>();
      Parents = Ctx.getParents(*E);
      continue;
    }
    break;
  }
  if (Parents.empty()) {
    // TODO: this is TOO frequent, because of how code is parsed. Implement
    // same at ASS time.
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

// inline llvm::MDNode *createFSanMD(std::string TyName, int64_t ArraySize,
//                                   clang::CodeGen::CodeGenFunction &CGF) {
//   llvm::LLVMContext &LLVMCtx = CGF.getLLVMContext();
//   llvm::MDNode *FSanMD = llvm::MDNode::get(
//       LLVMCtx, {
//                    llvm::MDString::get(LLVMCtx, "fsan.alloc"),
//                    llvm::MDString::get(LLVMCtx, TyName),
//                    llvm::ValueAsMetadata::get(llvm::ConstantInt::get(
//                        llvm::Type::getInt64Ty(LLVMCtx), ArraySize)),
//                });
//   return FSanMD;
// }

// /** Parses sizeof and assignment data. */
// inline void TagFromCallSite(const clang::CallExpr *E,
//                             clang::CodeGen::CodeGenFunction &CGF,
//                             clang::CodeGen::RValue Call,
//                             clang::CodeGen::CGCallee Callee) {
//   auto FNName = Callee.getFunctionPointer()->getName();

//   // reset pending type
//   if (CGF.PendingTypeIsValid) {
//     CGF.FSanPendingAllocType = clang::QualType();
//     CGF.PendingTypeIsValid = false;
//   }

//   if (FSAN::allocFunctions.count(FNName.str())) {
//     // dumpAllocSite(E, FNName, CGF);
//     auto ArraySize = -1;
//     for (const auto *Arg : E->arguments()) {
//       if (auto *unaryOperatorArg =
//               llvm::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(Arg)) {
//         if (unaryOperatorArg->getKind() == clang::UETT_SizeOf) {
//           // when the call has 1 sizeof arg, array size is 1
//           clang::QualType TypeToSize =
//           unaryOperatorArg->getTypeOfArgument(); TypeToSize =
//           CGF.getContext().getCanonicalType(TypeToSize);
//           // llvm::errs() << "TagFromCallSite: SIZEOF : "
//           //              << TypeToSize.getAsString() << ", SRC LOC: "
//           //              << Arg->getExprLoc().printToString(
//           //                     CGF.getContext().getSourceManager())
//           //              << "\n";
//           clang::QualType PointeeTy = TypeToSize;
//           llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
//           std::string IRTyNameStr = IRPointeeTy->isStructTy()
//                                         ?
//                                         IRPointeeTy->getStructName().str()
//                                         : "scalar";
//           llvm::StringRef IRPointeeTyName(IRTyNameStr);
//           CGF.FSanPendingAllocType = TypeToSize;
//           CGF.PendingTypeIsValid = true;
//           // llvm::errs()
//           //     << "[DBG-FSAN] This is a sizeof operator in the argument!
//           Type:
//           //     "
//           //     << TypeToSize.getAsString() << "\n";

//           if (auto *Instr =
//                   llvm::dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
//             ArraySize = 1;
//             llvm::MDNode *FSanMD =
//                 createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
//             Instr->setMetadata("fsan.alloc", FSanMD);
//             // llvm::errs()
//             //     << "\t\t[DBG-FSAN] fsan metadata attached to
//             //     instruction:\t\t";
//             // Instr->dump();
//             // llvm::errs() << "\n";
//           }
//         }
//       } else if (auto *binaryoperator =
//                      llvm::dyn_cast<clang::BinaryOperator>(Arg)) {
//         if (binaryoperator->getOpcode() == clang::BO_Mul) {
//           if (auto *RHS = llvm::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(
//                   binaryoperator->getRHS())) {
//             if (RHS->getKind() == clang::UETT_SizeOf) {
//               clang::QualType TypeToSize = RHS->getTypeOfArgument();
//               // llvm::errs()
//               //     << "RHS: This is a sizeof operator in the argument!
//               Type: "
//               //     << TypeToSize.getAsString() << ", SRC LOC: "
//               //     << RHS->getExprLoc().printToString(
//               //            CGF.getContext().getSourceManager())
//               //     << "\n";

//               //   llvm::LLVMContext &LLVMCtx = CGF.getLLVMContext();
//               clang::QualType PointeeTy = TypeToSize;
//               llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
//               std::string IRTyNameStr = IRPointeeTy->isStructTy()
//                                             ?
//                                             IRPointeeTy->getStructName().str()
//                                             : "scalar";
//               llvm::StringRef IRPointeeTyName(IRTyNameStr);
//               CGF.FSanPendingAllocType = TypeToSize;
//               CGF.PendingTypeIsValid = true;
//               // NOTE: we dont care about array size here
//               if (auto *Instr =
//                       llvm::dyn_cast<llvm::Instruction>(Call.getScalarVal()))
//                       {
//                 llvm::MDNode *FSanMD =
//                     createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
//                 // must be an instr. TODO: check if this is the case.
//                 Instr->setMetadata("fsan.alloc", FSanMD);
//                 // llvm::errs() << "\t\t[DBG-FSAN] fsan metadata attached
//                 to
//                 "
//                 //                 "instruction:\t\t";
//                 // Instr->dump();
//                 // llvm::errs() << "\n";
//               }
//             }

//           } else if (auto *LHS =
//                          llvm::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(
//                              binaryoperator->getLHS())) {
//             if (LHS->getKind() == clang::UETT_SizeOf) {
//               clang::QualType TypeToSize = LHS->getTypeOfArgument();
//               // llvm::errs()
//               //     << "LHS: This is a sizeof operator in the argument!
//               Type: "
//               //     << TypeToSize.getAsString() << ", SRC LOC: "
//               //     << LHS->getExprLoc().printToString(
//               //            CGF.getContext().getSourceManager())
//               //     << "\n";

//               //   llvm::LLVMContext &LLVMCtx = CGF.getLLVMContext();
//               clang::QualType PointeeTy = TypeToSize;
//               llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
//               std::string IRTyNameStr = IRPointeeTy->isStructTy()
//                                             ?
//                                             IRPointeeTy->getStructName().str()
//                                             : "scalar";
//               llvm::StringRef IRPointeeTyName(IRTyNameStr);
//               CGF.FSanPendingAllocType = TypeToSize;
//               CGF.PendingTypeIsValid = true;
//               if (auto *Instr =
//                       llvm::dyn_cast<llvm::Instruction>(Call.getScalarVal()))
//                       {
//                 // must be an instr. TODO: check if this is the case.
//                 llvm::MDNode *FSanMD =
//                     createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
//                 Instr->setMetadata("fsan.alloc", FSanMD);
//                 // llvm::errs() << "\t\t[DBG-FSAN] fsan metadata attached
//                 to
//                 "
//                 //                 "instruction:\t\t";
//                 // Instr->dump();
//                 // llvm::errs() << "\n";
//               }

//             } // LHS is sizeof
//           }
//         }
//       }
//     } // for arguments

//     auto info = FSAN::extractAssignment(E, CGF.getContext());
//     if (info) {
//       // llvm::errs() << "\t\t[FrontEnd] ASSIGNEE TYPE: "
//       //              << info->LHSType.getAsString()
//       //              << " POINTEE TYPE: " <<
//       info->PointeeType.getAsString()
//       //              << " IS DECLARATION: " << info->IsDeclaration <<
//       "\n";

//       if (Call.isScalar()) {
//         // Call.getScalarVal()->dump();
//         clang::QualType PointeeTy = info->PointeeType;
//         llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
//         std::string IRTyNameStr = IRPointeeTy->isStructTy()
//                                       ? IRPointeeTy->getStructName().str()
//                                       : "scalar";
//         // must match the one used for the Lookup
//         llvm::StringRef IRPointeeTyName(IRTyNameStr);
//         // bool isVoidPtr = info->LHSType->isVoidPointerType();

//         if (!CGF.PendingTypeIsValid) {
//           CGF.FSanPendingAllocType = PointeeTy;
//           CGF.PendingTypeIsValid = true;
//         }

//         // else return; // you are done if you found it

//         // if (auto *Instr =
//         // llvm::dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
//         //   // must be an instr. TODO: check if this is the case.
//         //   llvm::MDNode *FSanMD =
//         //       createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
//         //   Instr->setMetadata("fsan.alloc", FSanMD);
//         //   llvm::errs() << "\t\tMetadata attached to instruction:\n";
//         //   Instr->dump();
//         //   llvm::errs() << "\n";
//         // }
//         // LLM BS
//       } // if Call is scalar

//       // else if (Call.isComplex()) {
//       //   llvm::errs() << "TODO: handle Complex value:\n";
//       //   // Call.getComplexVal().first->dump();
//       //   // Call.getComplexVal().second->dump();
//       // } else if (Call.isAggregate()) {
//       //   llvm::errs() << "TODO: handle Aggregate at address: ";
//       //   // TODO: for later
//       //   // Call.getAggregateAddress()
//       // } else
//       //   llvm::errs() << "\t\t[FrontEnd] NO ASSIGNEE TYPE FOUND\n";
//     } // if info
//     else {
//       // NO ASSIGNMENT INFO AVAILABLE
//       // NOTE: it can happen not to find any sizeof or assignment
//       information at
//       // this time,  bail out in such a case
//       std::string dummyPorcodio = "porcodiotype";
//       std::string IRTyNameStr = "";
//       /**
//       std::string IRTyNameStr = IRPointeeTy->isStructTy()
//                                       ? IRPointeeTy->getStructName().str()
//                                       : "scalar"; */
//       if (!CGF.PendingTypeIsValid) {
//         // llvm::errs() << "\t\t[FrontEnd - TagFromCallSite] NoAss and no
//         // SizeOf: "
//         //                 "putting dummmy str for type str\n";
//         // // DONT BAIL OUT HERE, put guard value that tells next steps to
//         // // intervene
//         // llvm::errs() << "\t\t\tAllocation site: "
//         //              << E->getExprLoc().printToString(
//         //                     CGF.getContext().getSourceManager())
//         //              << ", in function: " << FNName << "\n";
//         IRTyNameStr = dummyPorcodio;
//       } // if no pending type
//       else {
//         // TYPE IS VALID
//         clang::QualType PendingTy = CGF.FSanPendingAllocType;
//         if (!PendingTy.isNull()) {
//           // llvm::errs() << "\t\t[FrontEnd] Applying pending type: "
//           //              << PendingTy.getAsString() << "\n";
//           clang::QualType PointeeTy;
//           if (PendingTy->isPointerType())
//             PointeeTy = PendingTy->getPointeeType();
//           else
//             PointeeTy = PendingTy;

//           llvm::Type *IRPointeeTy = CGF.ConvertTypeForMem(PointeeTy);
//           // llvm::errs() << "\t\t[FrontEnd] Applying pending type, IR
//           type:
//           "
//           //              << *IRPointeeTy << "\n";
//           IRTyNameStr = IRPointeeTy->isStructTy()
//                             ? IRPointeeTy->getStructName().str()
//                             : "scalar";
//         } // pending type is !null
//       } // pending type is valid
//       // at this point, that type could be null? TODO: check later

//       llvm::StringRef IRPointeeTyName(IRTyNameStr);
//       ArraySize = -1;
//       if (auto *Instr =
//               llvm::dyn_cast<llvm::Instruction>(Call.getScalarVal())) {
//         // must be an instr. TODO: check if this is the case.
//         llvm::MDNode *FSanMD =
//             createFSanMD(IRPointeeTyName.str(), ArraySize, CGF);
//         Instr->setMetadata("fsan.alloc", FSanMD);
//         // llvm::errs() << "\t\tMetadata attached to instruction:\n";
//         // Instr->dump();
//         // llvm::errs() << "\n";
//       } // if instr

//     } // when no assignment info
//   } // if function is allocation
// } // tagFromCallSite

// TODO: tag from assignment side?

} // namespace FSAN
#endif
