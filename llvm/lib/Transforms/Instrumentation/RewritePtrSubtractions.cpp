#include "llvm/Transforms/Instrumentation/RewritePtrSubtractions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"

using namespace llvm;

// define CL
cl::opt<bool> ClRewritePtrSubs(
    "rewrite-ptr-subs", cl::init(false),
    cl::desc(
        "Rewrite pointer subtractions to untag pointers before subtraction."));

void inline processOperand(Instruction *BOP, Value *OP, int idx,
                           uint64_t TagMaskByte, int PointerTagShift,
                           Module &M) {
  if (PtrToIntInst *PTI = dyn_cast<PtrToIntInst>(OP)) {
    // UNTAG
    uint64_t mask = ~(TagMaskByte << PointerTagShift);
    IRBuilder<> IRB(BOP);
    Value *MaskedPtrLong =
        IRB.CreateAnd(PTI, ConstantInt::get(PTI->getType(), mask));
    BOP->setOperand(idx, MaskedPtrLong);
  }
}
PtrToIntInst *getBasePTI(Value *V, int Depth = 0) {
  // Prevent infinite loops in case of phi nodes/cycles
  if (Depth > 5)
    return nullptr;

  // Base case: We found the ptrtoint!
  if (auto *PTI = dyn_cast<PtrToIntInst>(V)) {
    return PTI;
  }

  // If it's an instruction (like add, sub, mul), look at its operands
  if (auto *I = dyn_cast<Instruction>(V)) {
    switch (I->getOpcode()) {
    case Instruction::Add:
    case Instruction::Sub:
      // Check left operand
      if (auto *Left = getBasePTI(I->getOperand(0), Depth + 1))
        return Left;
      // Check right operand
      if (auto *Right = getBasePTI(I->getOperand(1), Depth + 1))
        return Right;
      break;
    // You can add logic for PHI nodes or Trunc/ZExt if needed
    default:
      break;
    }
  }

  return nullptr;
}

bool checkIfItsAPointer(Value *V) { return getBasePTI(V) != nullptr; }

bool RewritePtrSubtractionsPass::InstrumentBOP(BinaryOperator *BOP, Module &M) {
  auto DL = M.getDataLayout();
  auto *OP0 = BOP->getOperand(0);
  auto *OP1 = BOP->getOperand(1);
  {
    if (BOP->getOpcode() == Instruction::Add) {
      bool IsOp0Neg = OP0->hasName() &&
                      OP0->getName().str().find(".neg") != std::string::npos;
      bool IsOp1Neg = OP1->hasName() &&
                      OP1->getName().str().find(".neg") != std::string::npos;
      if (IsOp0Neg || IsOp1Neg) {
        assert(!(IsOp0Neg && IsOp1Neg) && "Both operands cannot be negations");
        Value *NegOp = IsOp0Neg ? OP0 : OP1;
        Value *OtherOp = IsOp0Neg ? OP1 : OP0;
        bool isOP0ptr = checkIfItsAPointer(OtherOp);
        bool isOP1ptr = checkIfItsAPointer(OtherOp);

        if ((isOP0ptr || isOP1ptr)) {
          // do something ...
          PtrToIntInst *PTIOther = getBasePTI(OtherOp);
          PtrToIntInst *PTINeg = getBasePTI(NegOp);
          if (PTIOther && PTINeg) {

            auto *PtrOther = PTIOther->getOperand(0);
            auto *PtrNeg = PTINeg->getOperand(0);

            IRBuilder<> IRBOther(PTIOther);
            auto *NewPtrOther = untagPointerIntrinsic(IRBOther, PtrOther, M);
            PTIOther->setOperand(0, NewPtrOther);

            IRBuilder<> IRBNeg(PTINeg);
            auto *NewPtrNeg = untagPointerIntrinsic(IRBNeg, PtrNeg, M);
            PTINeg->setOperand(0, NewPtrNeg);

            // errs() << "[FSAN] Instrumented BOP with negation: " << *BOP << "\n";
            return true;
          }
        }
      } // IsOp0Neg || IsOp1Neg
    }
  } // CASE ADDITION
  // if both operands are pointers, untag them before the subtraction
  bool BothPtr = false;
  BothPtr = dyn_cast<PtrToIntInst>(OP0) && dyn_cast<PtrToIntInst>(OP1);
  if (!BothPtr)
    return false;
  // errs() << "[==] Instrumenting BinaryOperator: " << *BOP
  //        << "  FUNC = " << BOP->getFunction()->getName() << "\n";
  processOperand(BOP, OP0, 0, TagMaskByte, PointerTagShift, M);
  processOperand(BOP, OP1, 1, TagMaskByte, PointerTagShift, M);
  return true;
}

Value *RewritePtrSubtractionsPass::untagPointerIntrinsic(IRBuilder<> &IRB,
                                                         Value *Ptr,
                                                         Module &M) {

  Type *PtrTy = Ptr->getType();
  unsigned PtrBits = M.getDataLayout().getPointerTypeSizeInBits(PtrTy);
  Type *MaskTy = IntegerType::get(M.getContext(), PtrBits);
  Value *MaskVal = ConstantInt::get(MaskTy, ~(TagMaskByte << PointerTagShift));

  Function *PtrMask =
      Intrinsic::getDeclaration(&M, Intrinsic::ptrmask, {PtrTy, MaskTy});
  Value *MaskedPtr = IRB.CreateCall(PtrMask, {Ptr, MaskVal});
  MaskedPtr->setName(Ptr->getName() + ".untagged");
  return MaskedPtr;
}

bool RewritePtrSubtractionsPass::InstrumentCMP(CmpInst *CI, Module &M) {
  /** Instrumenting CMPs with no filters */
  auto op1 = CI->getOperand(0);
  auto cmpType = op1->getType();
  auto op2 = CI->getOperand(1);
  if (cmpType->isPointerTy()) {
    // errs() << "[==] Instrumenting CmpInst: " << *CI
    //        << ", FUNC = " << CI->getFunction()->getName() << "\n";
    IRBuilder<> IRB(CI);
    Value *untaggedPtr1 = untagPointerIntrinsic(IRB, op1, M);
    CI->replaceUsesOfWith(op1, untaggedPtr1);
    Value *untaggedPtr2 = untagPointerIntrinsic(IRB, op2, M);
    CI->replaceUsesOfWith(op2, untaggedPtr2);
    return true;
  } else {
    auto NameOp1 = op1->hasName() ? op1->getName().str() : "";
    auto NameOp2 = op2->hasName() ? op2->getName().str() : "";
    if (NameOp1.find("magicptr") != std::string::npos ||
        NameOp2.find("magicptr") != std::string::npos) {
      // simplifycfg can generate CMPs where ptrs are cast directly to int and
      // have "magicptr" in their name
      IRBuilder<> IRB(CI);
      auto *Mask = ConstantInt::get(cmpType, ~(TagMaskByte << PointerTagShift));
      auto untaggedPtr1 = IRB.CreateAnd(op1, Mask);
      CI->replaceUsesOfWith(op1, untaggedPtr1);
      auto untaggedPtr2 = IRB.CreateAnd(op2, Mask);
      CI->replaceUsesOfWith(op2, untaggedPtr2);
      llvm::errs() << "[FSAN] Instrumented CMP with magicptr: " << *CI
                 << ", FUNC = " << CI->getFunction()->getName() << "\n";
      return true;
    }
    // else {
    //   if (NameOp1.find("sub.ptr") != std::string::npos &&
    //       NameOp2.find("sub.ptr") != std::string::npos) {
    //         errs() << "[FSAN] WARNING: UNINSTRUMENTED CMP WITH SUB.PTR: ";
    //         CI->print(errs());
    //         errs() << "OP0 " << *op1 << "\nOP1 " << *op2 << "\n";
    //         errs() << "\n";
    //         // instrument to dump operands at runtime

    //         IRBuilder<> IRB(CI);
    //         FunctionCallee DumpFcn = M.getOrInsertFunction(
    //             "printf",
    //             FunctionType::get(IntegerType::getInt32Ty(M.getContext()),
    //                                     PointerType::get(Type::getInt8Ty(M.getContext()),
    //                                     0), true));
    //         auto *FormatStr = IRB.CreateGlobalStringPtr(
    //             "CMP WITH SUB.PTR: OP0 %p, OP1 %p\n");
    //         IRB.CreateCall(DumpFcn, {FormatStr, op1, op2});
    //   }
    // }// else
  }
  return false;
} // InstrumentCMP

PreservedAnalyses RewritePtrSubtractionsPass::run(Module &M,
                                                  ModuleAnalysisManager &MAM) {
  bool changed = false;
  if (!ClRewritePtrSubs)
    return PreservedAnalyses::all();
  errs() << "[+] Running RewritePtrSubtractionsPass on module: " << M.getName()
         << "\n";
  for (Function &F : M) {
    for (BasicBlock &BB : F) {
      for (Instruction &I : BB) {
        if (I.getOpcode() == Instruction::Sub) {
          if (auto *BOP = dyn_cast<BinaryOperator>(&I)) {
            changed |= InstrumentBOP(BOP, M);
          } else
            assert(false && "Expected BinaryOperator for Sub instruction");
        }
        if (I.getOpcode() == Instruction::ICmp ||
            I.getOpcode() == Instruction::FCmp) {
          if (auto *CI = dyn_cast<CmpInst>(&I)) {
            changed |= InstrumentCMP(CI, M);
          } else
            assert(false && "Expected CmpInst for ICmp/FCmp instruction");
        }
      } // for Instruction
    } // for BB
  } // for Function
  return (changed ? PreservedAnalyses::none() : PreservedAnalyses::all());
} // run

// --- Plugin registration (new pass manager) ---

llvm::PassPluginLibraryInfo getPtrSubsRewritePassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "RewritePtrSubtractionsPass",
          LLVM_VERSION_STRING, [](PassBuilder &PB) {
            // Register as a module pass so we can call
            // getOrInsertFunction on Module
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "RewritePtrSubtractions") {
                    MPM.addPass(RewritePtrSubtractionsPass());
                    return true;
                  }
                  return false;
                });

            // Optionally run early in the optimization pipeline
            PB.registerPipelineStartEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel) {
                  MPM.addPass(RewritePtrSubtractionsPass());
                });
          }};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getPtrSubsRewritePassPluginInfo();
}