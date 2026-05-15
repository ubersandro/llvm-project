// llvm/lib/Transforms/Instrumentation/RewritePtrSubtractions.h
#ifndef LLVM_TRANSFORMS_INSTRUMENTATION_FSANREWRITEPTRSUBTRACTIONS_H
#define LLVM_TRANSFORMS_INSTRUMENTATION_FSANREWRITEPTRSUBTRACTIONS_H
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"

namespace llvm {

struct RewritePtrSubtractionsPass
    : public PassInfoMixin<RewritePtrSubtractionsPass> {

  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);

private:
  bool InstrumentBOP(BinaryOperator *BOP, Module &M);
  bool InstrumentCMP(CmpInst *CI, Module &M);
  Value *untagPointerIntrinsic(IRBuilder<> &IRB, Value *Ptr, Module &M);

#if defined(__aarch64__)
  uint64_t TagMaskByte = 0xFF;
  uint64_t PointerTagShift = 56;
#else
  uint64_t TagMaskByte = 0x3F;
  uint64_t PointerTagShift = 57;
#endif
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_INSTRUMENTATION_FSANREWRITEPTRSUBTRACTIONS_H