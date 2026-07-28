/** This file is part of custom HWAsan - FSAN */
#ifndef FSAN_TAGGING_RUNTIME_SUPPORT_H
#define FSAN_TAGGING_RUNTIME_SUPPORT_H

#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <deque>
#include <sys/types.h>
using namespace llvm;

namespace RuntimeTaggingSupport {
Value *RetrieveOrCreateTagVector(Type* TY, Module &M, int depth = 0);
u_int8_t *ComputeTags(StructType *Ty, Module &M, int depth = 0, u_int8_t * Tags = nullptr);
void ComputeTagsOnNDArray(ArrayType *Ty, Module &M, const DataLayout &DL, int depth = 0, u_int8_t *Tags = nullptr, uint64_t BaseOffset = 0);

void createTagVector(Type *TY, Module &M, int depth = 0);
} // namespace RuntimeTaggingSupport

#endif