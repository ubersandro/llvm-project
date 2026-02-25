// llvm/lib/Transforms/Instrumentation/FSanRewriteFunctionCalls.h
#ifndef LLVM_TRANSFORMS_INSTRUMENTATION_FSANREWRITEFUNCTIONCALLS_H
#define LLVM_TRANSFORMS_INSTRUMENTATION_FSANREWRITEFUNCTIONCALLS_H

#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"

namespace llvm {

struct FSanRewriteFunctionCallsPass
    : public PassInfoMixin<FSanRewriteFunctionCallsPass> {

  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);

private:
  bool isTypedMallocLike(CallBase *CB);
  bool isTypedNewOperator(CallBase *CB);
  bool RewriteCallToTypedAllocator(CallBase *CB, Module &M);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_INSTRUMENTATION_FSANREWRITEFUNCTIONCALLS_H