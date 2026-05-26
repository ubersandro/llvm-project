// llvm/lib/Transforms/Instrumentation/FSanRewriteFunctionCalls.h
#ifndef LLVM_TRANSFORMS_INSTRUMENTATION_FSANREWRITEFUNCTIONCALLS_H
#define LLVM_TRANSFORMS_INSTRUMENTATION_FSANREWRITEFUNCTIONCALLS_H

#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#if defined(__aarch64__)
#define BITS 7
#else
#define BITS 5
#endif
namespace llvm {

struct FSanRewriteFunctionCallsPass
    : public PassInfoMixin<FSanRewriteFunctionCallsPass> {

  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);
private:
  uint64_t RPTag = 1ULL << BITS; 
  bool isTypedMallocLike(CallBase *CB);
  bool isTypedNewOperator(CallBase *CB);
  // bool InstrumentBOP(BinaryOperator *BOP);
  // bool InstrumentCMP(CmpInst *CI);
  bool ProcessMallocLikeCall(CallBase *CB, Module &M);
  bool ProcessNewCall(CallBase *I, Module &M);
};

}

#endif // LLVM_TRANSFORMS_INSTRUMENTATION_FSANREWRITEFUNCTIONCALLS_H