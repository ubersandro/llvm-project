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

bool RewritePtrSubtractionsPass::InstrumentBOP(BinaryOperator *BOP, Module &M) {
  
  auto DL = M.getDataLayout();
  auto *OP0 = BOP->getOperand(0);
  auto *OP1 = BOP->getOperand(1);
  // if both operands are pointers, untag them before the subtraction
  bool BothPtr = false;
  BothPtr = dyn_cast<PtrToIntInst>(OP0) && dyn_cast<PtrToIntInst>(OP1);
  if (!BothPtr)
    return false;
  errs() << "[==] Instrumenting BinaryOperator: " << *BOP
         << "  FUNC = " << BOP->getFunction()->getName() << "\n";
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
    errs() << "[==] Instrumenting CmpInst: " << *CI
           << ", FUNC = " << CI->getFunction()->getName() << "\n";
    IRBuilder<> IRB(CI);
    Value *untaggedPtr1 = untagPointerIntrinsic(IRB, op1, M);
    CI->replaceUsesOfWith(op1, untaggedPtr1);
    Value *untaggedPtr2 = untagPointerIntrinsic(IRB, op2, M);
    CI->replaceUsesOfWith(op2, untaggedPtr2);
    return true;
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