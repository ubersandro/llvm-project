#include "llvm/Transforms/Instrumentation/FSanRewriteFunctionCalls.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Instrumentation/RuntimeTaggingSupport.hpp"
#include <cstdint>
#include <deque>
#include <sys/types.h>
using namespace llvm;

#define DEBUG_TYPE "fsan-rewrite"
STATISTIC(NumCallsRewritten, "Number of allocator calls rewritten");

static cl::opt<bool> ClInstrumentHeap("fsan-heaporcodio",
                                      cl::desc("instrument heap"), cl::Hidden,
                                      cl::init(false));

bool FSanRewriteFunctionCallsPass::isTypedMallocLike(CallBase *CB) {
  Value *V = CB->getCalledOperand()->stripPointerCasts();
  Function *Callee = dyn_cast<Function>(V);
  auto demangledName = Callee ? llvm::demangle(Callee->getName().str()) : "";
  return (Callee &&
          demangledName.find("typed_allocation") != std::string::npos) &&
         ClInstrumentHeap; // label for typed fnctn
}

bool FSanRewriteFunctionCallsPass::isTypedNewOperator(CallBase *CB) {
  Value *V = CB->getCalledOperand()->stripPointerCasts();
  Function *Callee = dyn_cast<Function>(V);
  auto demangledName = Callee ? llvm::demangle(Callee->getName().str()) : "";
  return (Callee && demangledName.find("operator new") != std::string::npos &&
          demangledName.find("align_val_t") == std::string::npos) &&
         ClInstrumentHeap;
}

bool doCheckOnCookie(Value *V) {
  if (Constant *name = dyn_cast<Constant>(V)) {
    if (ConstantDataArray *dataArray =
            dyn_cast<ConstantDataArray>(name->getOperand(0))) {
      if (dataArray->isString()) {
        StringRef str = dataArray->getAsString();
        // remove trailing nullbyte
        std::string pinoPalettaStr = str.str().substr(0, str.size() - 1);
        return pinoPalettaStr ==
               "PINO_PALETTA"; // Q: will this work with null term?
      }
    }
  }

  return false;
}

CallBase *rewriteCall(CallBase *CI, StructType *allocType, Value *arraySize,
                      const std::string &formerAllocatorName, Module &M,
                      bool *needsOffsetForCookie = nullptr) {
  bool isNew = false;
  Value *allocSize = nullptr;
  Value *nElems = nullptr;
  Value *origPtr = nullptr;
  LLVMContext &Ctx = M.getContext();
  Type *SizeTy = M.getDataLayout().getIntPtrType(Ctx); // use for size
  Type *VoidPtrTy = CI->getType();                     // opaque
  FunctionCallee formerFn;
  bool isRealloc = false;
  bool hasAlignment = false;
  if (formerAllocatorName == "malloc") {
    allocSize = CI->getArgOperand(0);
  } // malloc
  else if (formerAllocatorName == "realloc") {
    origPtr = CI->getArgOperand(0);
    allocSize = CI->getArgOperand(1);
    isRealloc = true;
  } // realloc
  else if (formerAllocatorName == "calloc") {
    allocSize = CI->getArgOperand(1);
    nElems = CI->getArgOperand(0);
  } // calloc
  else if (formerAllocatorName == "reallocarray") {
    origPtr = CI->getArgOperand(0);
    nElems = CI->getArgOperand(1);
    allocSize = CI->getArgOperand(2);
  } // reallocarray
  else if (formerAllocatorName.find("operator new[]") != std::string::npos) {
    allocSize = CI->getArgOperand(0);
    isNew = true;
    // TODO: does it have alignment?? Only if 3 params there is alignment
    auto callArgsNum = CI->arg_size();
    if (callArgsNum == 3) {
      // it has type and alignment
      hasAlignment = true; // TODO
    }
  } // operator new[]
  else if (formerAllocatorName.find("operator new") != std::string::npos) {
    allocSize = CI->getArgOperand(0);
    isNew = true;
    auto callArgsNum = CI->arg_size();
    if (callArgsNum == 3) {
      // it has type and alignment
      hasAlignment = true; // TODO
    }
  } // operator new
  // TODO: handle memalign, aligned_alloc, posix_memalign, valloc, pvalloc

  Type *sizeType = allocSize->getType();

  // adjust arguments && former function
  SmallVector<Value *, 4> arguments;
  if (formerAllocatorName == "malloc") {
    FunctionType *MallocType = FunctionType::get(VoidPtrTy, {sizeType}, false);
    formerFn = M.getOrInsertFunction("malloc", MallocType);
    assert(formerFn && "Failed to get or insert malloc function");
    arguments.push_back(allocSize);
  }

  if (formerAllocatorName == "calloc") {
    formerFn = M.getOrInsertFunction("calloc", VoidPtrTy, sizeType, sizeType);
    arguments.push_back(nElems);
    arguments.push_back(allocSize);
  }

  if (formerAllocatorName == "realloc") {
    FunctionType *ReallocTy =
        FunctionType::get(VoidPtrTy, {VoidPtrTy, sizeType}, false);

    formerFn = M.getOrInsertFunction("realloc", ReallocTy);
    assert(formerFn && "Failed to get or insert realloc function");
    arguments.push_back(origPtr);
    arguments.push_back(allocSize);
  }

  if (formerAllocatorName == "reallocarray") {
    formerFn = M.getOrInsertFunction("reallocarray", VoidPtrTy, VoidPtrTy,
                                     sizeType, sizeType);
    arguments.push_back(origPtr);
    arguments.push_back(nElems);
    arguments.push_back(allocSize);
  }
  if (formerAllocatorName.find("operator new[]") != std::string::npos ||
      formerAllocatorName.find("operator new") != std::string::npos) {

    // TODO: check on std::throw arg, if still there!
    bool cookieStrIsThere = false;
    cookieStrIsThere = doCheckOnCookie(CI->getArgOperand(CI->arg_size() - 1));
    // if (cookieStrIsThere)
    //   errs() << "COOKIE ACK IN IR\n";
    unsigned originalArgsNum =
        cookieStrIsThere ? CI->arg_size() - 2 : CI->arg_size() - 1;
    *needsOffsetForCookie = cookieStrIsThere;

    for (unsigned i = 0; i < originalArgsNum; ++i)
      arguments.push_back(CI->getArgOperand(i));
  }

  if (isNew) {
    bool isInvoke = isa<InvokeInst>(CI);
    if (isInvoke) {
      InvokeInst *OldInv = cast<InvokeInst>(CI);
      IRBuilder<> IRB(OldInv->getParent(), OldInv->getIterator());
      auto *Dest = OldInv->getNormalDest();
      auto *UnwindDest = OldInv->getUnwindDest();
      Value *OldInvokedFunc = OldInv->getCalledOperand()->stripPointerCasts();
      FunctionType *OldInvokedFuncTy = nullptr;
      if (Function *OldInvokedFuncAsFn = dyn_cast<Function>(OldInvokedFunc)) {
        OldInvokedFuncTy = OldInvokedFuncAsFn->getFunctionType();
      }

      assert(OldInvokedFuncTy &&
             "Failed to get function type of old invoked function");
      InvokeInst *NewInvoke =
          InvokeInst::Create(OldInvokedFuncTy, OldInv->getCalledOperand(), Dest,
                             UnwindDest, arguments, "invoke.rewrite");
      // TODO: REFACTOR and fix attributes to function call to match
      // original!
      NewInvoke->setDebugLoc(OldInv->getDebugLoc());
      NewInvoke->insertBefore(OldInv);
      OldInv->replaceAllUsesWith(NewInvoke);

      OldInv->eraseFromParent();
      return NewInvoke;
    } else {
      // its a new call

      Value *NewOperator = CI->getCalledOperand()->stripPointerCasts();
      FunctionType *NewOperatorTy = nullptr;
      if (Function *NewOperatorAsFn = dyn_cast<Function>(NewOperator)) {
        NewOperatorTy = NewOperatorAsFn->getFunctionType();
      }
      assert(NewOperatorTy &&
             "Failed to get function type of new operator function");

      CallInst *NewCall = CallInst::Create(
          NewOperatorTy, CI->getCalledOperand(), arguments, "call.rewrite");
      NewCall->setTailCall(true);
      NewCall->setDebugLoc(CI->getDebugLoc());

      NewCall->insertBefore(CI);
      CI->replaceAllUsesWith(NewCall);
      CI->eraseFromParent();
      return NewCall;
    }

    return nullptr;
  } // if isNew

  if (InvokeInst *Invoke = dyn_cast<InvokeInst>(CI)) {
    // INVOKE MALLOC
    InvokeInst *OldInv = cast<InvokeInst>(CI);

    IRBuilder<> IRB(OldInv->getParent(), OldInv->getIterator());
    auto *Dest = OldInv->getNormalDest();
    auto *UnwindDest = OldInv->getUnwindDest();
    Value *OldInvokedFunc; // = OldInv->getCalledOperand()->stripPointerCasts();
    FunctionType *OldInvokedFuncTy = nullptr;

    // FETCH MALLOC SIGNATURE IF IT's MALLOC
    if (formerAllocatorName == "malloc") {
      OldInvokedFunc = M.getFunction("malloc");
    }
    if (formerAllocatorName == "calloc") {
      OldInvokedFunc = M.getFunction("calloc");
    }
    if (formerAllocatorName == "realloc") {
      OldInvokedFunc = M.getFunction("realloc");
    } else
      assert(false &&
             "TODO  handle other allocators for invoke, currently only malloc");
    if (Function *OldInvokedFuncAsFn = dyn_cast<Function>(OldInvokedFunc)) {
      OldInvokedFuncTy = OldInvokedFuncAsFn->getFunctionType();
    }

    assert(OldInvokedFuncTy &&
           "Failed to get function type of old invoked function");

    InvokeInst *NewInvoke =
        InvokeInst::Create(OldInvokedFuncTy, OldInvokedFunc, Dest, UnwindDest,
                           arguments, "invoke.rewrite");
    NewInvoke->setDebugLoc(OldInv->getDebugLoc());
    NewInvoke->insertBefore(OldInv);
    OldInv->replaceAllUsesWith(NewInvoke);
    OldInv->eraseFromParent();
    return NewInvoke;
  }
  IRBuilder<> IRB(CI);
  CallBase *formerCall = IRB.CreateCall(formerFn, arguments);
  CI->replaceAllUsesWith(formerCall);
  // TODO: debug attributes, maybe you need to set some!
  CI->eraseFromParent();
  NumCallsRewritten++;
  return formerCall;
}

// TODO: refactor
Value *GetArraySize(CallBase *CI, std::string demangledName, Module &M,
                    StructType *t, IRBuilder<> &IRB) {
  assert(!demangledName.empty() && "Demangled name cannot be empty");
  uint64_t typeSize = M.getDataLayout().getTypeAllocSize(t);

  if (typeSize == 0) {
    // TODO: debug this corner case, prevent it by design
    errs() << "Error: Type size is zero for type " << t->getName() << "\n";
    errs() << "isOpaque = " << t->isOpaque() << "\n";
    errs() << "Type dump:\n";
    errs() << *t << "\n";
    assert(typeSize != 0 &&
           "Type size cannot be zero for allocation size reconstruction");
  }
  auto Int64Ty = Type::getInt64Ty(M.getContext());
  PointerType *PtrTy = PointerType::getUnqual(M.getContext());

  Value *TypeSizeValue =
      ConstantInt::get(Int64Ty, typeSize); // size of the struct type
  if (demangledName == "malloc" || demangledName == "valloc" ||
      demangledName == "pvalloc") {
    Value *MallocSizeValue = IRB.CreateZExt(CI->getArgOperand(0), Int64Ty);
    return IRB.CreateUDiv(MallocSizeValue, TypeSizeValue);
  } else if (demangledName == "calloc") {
    return IRB.CreateZExt(CI->getArgOperand(0), Int64Ty);
  } else if (demangledName == "realloc") {
    Value *ReallocSizeValue = IRB.CreateZExt(CI->getArgOperand(1), Int64Ty);
    return IRB.CreateUDiv(ReallocSizeValue, TypeSizeValue);
  } else if (demangledName == "reallocarray") {
    return IRB.CreateZExt(CI->getArgOperand(1), Int64Ty);
  } else if (demangledName.find("operator new") != std::string::npos) {
    bool isArrayNew = (demangledName.find("new[]") != std::string::npos);
    Value *NewSizeValue = IRB.CreateZExt(CI->getArgOperand(0), Int64Ty);
    if (isArrayNew) {
      return IRB.CreateUDiv(NewSizeValue, TypeSizeValue);
    } else {
      return ConstantInt::get(Int64Ty, 1);
    }
  }

  assert(false && "Allocator not handled for size reconstruction");
  return nullptr;
}

// TODO: refactor
// NOTE: mallocs can be performed on ptr additions
bool FSanRewriteFunctionCallsPass::ProcessMallocLikeCall(CallBase *CI,
                                                         Module &M) {
  assert(false && "malloc NOPE");
  auto Int64Ty = Type::getInt64Ty(M.getContext());
  PointerType *PtrTy = PointerType::getUnqual(M.getContext());
  StructType *allocType = nullptr;
  std::string structName = "";
  std::string formerAllocatorName = "";

  Value *strPtr = nullptr;
  Value *arraySize = nullptr;
  Value *formerFunction = nullptr;

  auto nArgs = CI->arg_size();
  if (nArgs < 3) {
    return false;
  }

  int strIdx = (int)nArgs - 3;
  int arraySizeIdx = (int)nArgs - 2;
  int formerFunctionIdx = (int)nArgs - 1;

  for (unsigned i = 0; i < CI->arg_size(); i++) {
    Value *arg = CI->getArgOperand(i);
    if ((int)i == strIdx)
      strPtr = arg;
    if ((int)i == arraySizeIdx)
      arraySize = arg;
    if ((int)i == formerFunctionIdx)
      formerFunction = arg;
  }

  if (!strPtr || !arraySize || !formerFunction)
    assert(false &&
           "Failed to extract necessary arguments for typed allocator call");

  // flag to skip tagging if not a struct/class or if union
  bool dontTag = false;
  if (Constant *name = dyn_cast<Constant>(strPtr)) {
    if (ConstantDataArray *dataArray =
            dyn_cast<ConstantDataArray>(name->getOperand(0))) {
      if (dataArray->isString()) {
        StringRef structNameRef = dataArray->getAsString();
        bool hasNullTerminator =
            !structNameRef.empty() && structNameRef.back() == '\0';
        if (hasNullTerminator)
          structName = structNameRef.str().substr(0, structNameRef.size() - 1);

        if (structName.find("struct") != std::string::npos ||
            structName.find("class") != std::string::npos) {
          allocType = StructType::getTypeByName(CI->getModule()->getContext(),
                                                structName);
          assert(allocType && "Failed to find struct type by name in module");
          dontTag = false;
        } // it's struct or class
        else {
          if (structName.find("union") != std::string::npos) {
            dontTag = true;
          } else {
            dontTag = true;
          }
        }
      }
    }
  }

  // --- Decode former function name from formerFunction ---
  if (Constant *name = dyn_cast<Constant>(formerFunction)) {
    if (ConstantDataArray *dataArray =
            dyn_cast<ConstantDataArray>(name->getOperand(0))) {
      if (dataArray->isString()) {
        StringRef ref = dataArray->getAsString();
        formerAllocatorName = ref.str();
        formerAllocatorName =
            formerAllocatorName.substr(0, formerAllocatorName.size() - 1);
      }
    }
  }

  // this is a destructive operation for CI
  CallBase *formerCall =
      rewriteCall(CI, allocType, arraySize, formerAllocatorName, M);
  assert(formerCall &&
         "Failed to rewrite malloc-like call to former allocator");

  CallBase *newCI = dyn_cast<CallBase>(formerCall);
  assert(newCI && "Expected the rewritten call to be an instruction");
  auto oldName = newCI->hasName() ? newCI->getName().str() : "noname";
  newCI->setName(oldName + ".fieldarmor.rewrite");
  bool changed = true;

  if (allocType && !dontTag && ClInstrumentHeap && !allocType->isOpaque()) {
    auto *NextInst = newCI->getNextNonDebugInstruction();
    Instruction *InsertPt = nullptr;
    BasicBlock *BB;

    if (InvokeInst *Invoke = dyn_cast<InvokeInst>(newCI)) {
      BasicBlock *NormalDest = Invoke->getNormalDest();
      if (NormalDest)
        InsertPt = &NormalDest->front(); // insert at the beginning
                                         // of the normal dest block
      else
        InsertPt = Invoke; // fallback to inserting after the invoke
                           // if no normal dest
    } else
      InsertPt = newCI->getNextNonDebugInstruction(); // insert right after
                                                      // the new call
    // if (!NextInst) {
    //   // TODO: instrument as done with INVOKE
    //   // set BB
    //   // set InsertPt

    // } else {
    //   Instruction *Last = cast<CallInst>(newCI); // your
    //   %.fieldarmor.rewrite BB = Last->getParent(); InsertPt =
    //   std::next(Last->getIterator()); while (InsertPt != BB->end() &&
    //   InsertPt->isDebugOrPseudoInst())
    //     ++InsertPt;
    // }

    IRBuilder<> IRB(InsertPt);
    Value *ArraySize;
    int32_t extractedArraySize = 0;
    if (ConstantInt *CInt = dyn_cast<ConstantInt>(arraySize)) {
      extractedArraySize = CInt->getZExtValue();
      if (extractedArraySize != -1)
        ArraySize = ConstantInt::get(Int64Ty, extractedArraySize);
      else
        ArraySize = GetArraySize(newCI, formerAllocatorName, M, allocType, IRB);
    } else
      ArraySize = GetArraySize(newCI, formerAllocatorName, M, allocType, IRB);
    assert(ArraySize != nullptr &&
           "Failed to compute array size for typed allocation");

    TypeSize tSize = M.getDataLayout().getTypeAllocSize(allocType);
    // now tag with tagging function
    FunctionCallee fsan_tag_memory = M.getOrInsertFunction(
        "fsan_tag_memory", Int64Ty, PtrTy, PtrTy, Int64Ty, Int64Ty);
    auto *TagVector =
        RuntimeTaggingSupport::RetrieveOrCreateTagVector(allocType, M);
    assert(TagVector &&
           "Failed to retrieve or create tag vector for struct type");
    auto *call = IRB.CreateCall(fsan_tag_memory,
                                {IRB.CreatePointerCast(newCI, PtrTy),
                                 IRB.CreatePointerCast(TagVector, PtrTy),
                                 ConstantInt::get(Int64Ty, tSize), ArraySize});
    // llvm::errs() << "[FieldArmor] TAGGING ALLOC:\n\t" << *newCI
    //              << "\n\t\tSTRUCT: " << allocType->getStructName()
    //              << "\n\t\tARR_SZ: " << *ArraySize << "\n";
  }
  return changed;
}

void doQuickCheckOnMD(CallBase *I) {
  auto *FsanMD = I->getMetadata("fsan.new");
  bool mdPresent = (FsanMD != nullptr);
  if (mdPresent) {
    // NOTE: just assuming MD are there is bad, too much unpredictability
    // due to optimizations. What if I patch some passes and then others
    // just break things?
    llvm::errs() << "\t\t[IR] MD HIT ON: " << *I << "\n";
  } else {
    llvm::errs() << "\t\t[IR] NO MD ON: " << *I << ", ";
    // SRC
    if (DILocation *Loc = I->getDebugLoc()) {
      llvm::errs() << "\tSRC: " << Loc->getFilename() << ":" << Loc->getLine()
                   << "\n";
    }
  }
}
void dbgSrcAndUses(CallBase *I) {
  {
    // dump src location from dbg
    if (DILocation *Loc = I->getDebugLoc()) {
      llvm::errs() << "\tSource location: " << Loc->getFilename() << ":"
                   << Loc->getLine() << "\n";
    }
    for (auto *user : I->users()) {
      if (InvokeInst *invoke = dyn_cast<InvokeInst>(user)) {
        Value *V = invoke->getCalledOperand()->stripPointerCasts();
        Function *Invokee = dyn_cast<Function>(V);
        if (Invokee) {
          auto demangledNameOfInvoke = demangle(Invokee->getName().str());
          // llvm::errs() << "\tINVOKE USR: " << demangledNameOfInvoke <<
          // "\n";
        }
      }
    }
  }
}

bool FSanRewriteFunctionCallsPass::ProcessNewCall(CallBase *I, Module &M) {
  assert(false && "new NOPE");

  Value *V = I->getCalledOperand()->stripPointerCasts();
  bool changed = false;
  Function *Callee = dyn_cast<Function>(V);
  if (Callee) {
    StringRef name = Callee->getName();
    std::string demangledName = demangle(Callee->getName().str());

    if (demangledName.find("nothrow") != std::string::npos) {
      // TODO: debug this corner case
      // llvm::errs() << "\t\t[IR] NOTHROW NEW, skipping for now\n";
      return false;
    }

    auto size = I->arg_size();
    if (size <= 1) {
      // llvm::errs() << "\t\t[IR] NOT ENOUGH ARGS FOR NEW, skipping: " << *I
      //              << "\n";
      return false;
    } // size guard

    bool cookieIsThere = doCheckOnCookie(I->getArgOperand(size - 1));
    auto lastArg =
        cookieIsThere
            ? I->getArgOperand(I->arg_size() - 2)
            : I->getArgOperand(I->arg_size() - 1); // typeName or COOKIE!!!

    std::string structName = "";
    StructType *allocType = nullptr;

    if (Constant *name = dyn_cast<Constant>(lastArg)) {
      if (ConstantDataArray *dataArray =
              dyn_cast<ConstantDataArray>(name->getOperand(0))) {
        if (dataArray->isString()) {
          StringRef structNameRef = dataArray->getAsString();
          std::string structName =
              structNameRef.str().substr(0, structNameRef.size() - 1);
          allocType =
              StructType::getTypeByName(Callee->getContext(), structName);
        } else {

          if (PHINode *phi = dyn_cast<PHINode>(lastArg)) {
            auto *name = phi->getIncomingValue(0);
            if (Constant *nameConst = dyn_cast<Constant>(name)) {
              if (ConstantDataArray *dataArray =
                      dyn_cast<ConstantDataArray>(nameConst->getOperand(0))) {
                if (dataArray->isString()) {
                  StringRef structNameRef = dataArray->getAsString();
                  std::string structName =
                      structNameRef.str().substr(0, structNameRef.size() - 1);
                  allocType = StructType::getTypeByName(Callee->getContext(),
                                                        structName);
                }
              }
            }
          } else
            assert(false && "Expected last argument to be a string constant in "
                            "ProcessNewCall");
        }
      }
    } // if constant last arg

    bool needsOffsetForCookie = false;
    CallBase *NewCI = rewriteCall(I, allocType, nullptr, demangledName, M,
                                  &needsOffsetForCookie);
    bool isUnion =
        (!structName.empty() && structName.find("union") != std::string::npos);
    if (isUnion) {
      return true; // we are not rewriting here!!!!
    }

    { // do the tagging
      if (allocType && allocType->isStructTy() && ClInstrumentHeap &&
          !allocType->isOpaque()) {
        Instruction *InsertPt = nullptr;

        if (InvokeInst *Invoke = dyn_cast<InvokeInst>(NewCI)) {
          BasicBlock *NormalDest = Invoke->getNormalDest();
          if (NormalDest)
            InsertPt = &NormalDest->front(); // insert at the beginning
                                             // of the normal dest block
          else
            InsertPt = Invoke; // fallback to inserting after the invoke
                               // if no normal dest
        } else
          InsertPt = NewCI->getNextNonDebugInstruction(); // insert right after
                                                          // the new call
        assert(InsertPt && "Failed to find insertion point for tagging after "
                           "new operator call");
        IRBuilder<> IRB(InsertPt);

        // TODO: check on array size post FP
        Value *ArraySize =
            GetArraySize(NewCI, demangledName, M, allocType, IRB);
        assert(ArraySize != nullptr &&
               "Failed to compute array size for typed allocation");
        TypeSize tSize = M.getDataLayout().getTypeAllocSize(allocType);
        auto Int64Ty = Type::getInt64Ty(M.getContext());
        PointerType *PtrTy = PointerType::getUnqual(M.getContext());
        FunctionCallee fsan_tag_memory = M.getOrInsertFunction(
            "fsan_tag_memory", Int64Ty, PtrTy, PtrTy, Int64Ty, Int64Ty);
        auto *TagVector =
            RuntimeTaggingSupport::RetrieveOrCreateTagVector(allocType, M);
        assert(TagVector &&
               "Failed to retrieve or create tag vector for struct type");
        Value *whereToTagFrom = NewCI;
        bool isNewArray = demangledName.find("new[]") != std::string::npos;
        Value *Offset = nullptr;

        if (isNewArray && needsOffsetForCookie) {
          Offset = IRB.CreateGEP(IRB.getInt8Ty(), // element type: i8 (1
                                                  // byte per index unit)
                                 NewCI,           // base pointer
                                 IRB.getInt64(8), // offset by 8 bytes
                                 "cookie_ptr");
          whereToTagFrom = Offset;
        }

        auto *Tagged = IRB.CreateCall(
            fsan_tag_memory, {IRB.CreatePointerCast(whereToTagFrom, PtrTy),
                              IRB.CreatePointerCast(TagVector, PtrTy),
                              ConstantInt::get(Int64Ty, tSize), ArraySize});
        // llvm::errs() << "[FieldArmor] TAGGING NEW:\n\t" << *NewCI
        //              << "\n\t\tSTRUCT: " << allocType->getStructName()
        //              << "\n\t\tARR_SZ: " << *ArraySize << "\n";
        Tagged->setName(NewCI->getName() + ".tagged");
        // NewCI->replaceUsesWithIf(Tagged, [NewCI, Offset](const Use &U) {
        //   auto *User = U.getUser();
        //   bool isCallToFSANTagMemory =
        //       isa<CallInst>(User) &&
        //       cast<CallInst>(User)->getCalledFunction() &&
        //       cast<CallInst>(User)->getCalledFunction()->hasName() &&
        //       cast<CallInst>(User)->getCalledFunction()->getName().str().find(
        //           "fsan_tag_memory") != std::string::npos;
        //   bool safe = !isa<LifetimeIntrinsic>(User);
        //   safe &= !isa<DbgInfoIntrinsic>(User);
        //   safe &= !isCallToFSANTagMemory;
        //   safe &= (Offset!=nullptr && User != Offset) || Offset == nullptr;
        //   return safe;
        // });
        changed = true;
      } // if allocType
      else
        return changed;
    } // do the tagging

  } // if Callee
  else {
    assert(false && "Expected a function call in ProcessNewCall");
  }
  return changed;
} // ProcessNewCall

// double check that there are no REALLOC,  MALLOC etc
void doQuickCheck(CallBase *CI) {
  Value *V = CI->getCalledOperand()->stripPointerCasts();
  Function *Callee = dyn_cast<Function>(V);
  if (Callee) {
    StringRef name = Callee->getName();
    std::string demangledName = demangle(Callee->getName().str());
    if (demangledName == "malloc" || demangledName == "realloc" ||
        demangledName == "calloc" || demangledName == "reallocarray" ||
        demangledName == "memalign" || demangledName == "aligned_alloc" ||
        demangledName == "posix_memalign" || demangledName == "valloc" ||
        demangledName == "pvalloc") {
      auto nuses = CI->getNumUses();
      if (nuses > 0) {
        // TODO: check if you can do something about this corner case
      }
    }
  }
}

void FSanRewriteFunctionCallsPass::debugCMP(CmpInst *cmp, Module &M) {
  // FunctionCallee printfFunc = M.getOrInsertFunction(
  //     "printf", FunctionType::get(IntegerType::getInt32Ty(M.getContext()),
  //                                PointerType::getUnqual(M.getContext()),
  //                                true));
  // auto * CmpType = cmp->getOperand(0)->getType();
  // if(CmpType->isPointerTy()){
  //   IRBuilder<> IRB(cmp->getNextNonDebugInstruction());
  //   Value *OP0 = cmp->getOperand(0);
  //   Value *OP1 = cmp->getOperand(1);
  //   Value *typeStr = IRB.CreateGlobalStringPtr(cmp->getOpcodeName());
  //   Value *FormatStr = IRB.CreateGlobalStringPtr("CMP-%s: %llx, %p\n");
  //   PointerType *PtrTy = PointerType::getUnqual(M.getContext());
  //   IRB.CreateCall(printfFunc, {FormatStr, IRB.CreatePointerCast(OP0, PtrTy),
  //   IRB.CreatePointerCast(OP1, PtrTy)});
  // }
}
void FSanRewriteFunctionCallsPass::debugBOP(BinaryOperator *binOp, Module &M) {
  // dump the operands in hex
  FunctionCallee printfFunc = M.getOrInsertFunction(
      "printf",
      FunctionType::get(IntegerType::getInt32Ty(M.getContext()),
                        PointerType::getUnqual(M.getContext()), true));
  auto *Op0 = binOp->getOperand(0);
  auto *Op1 = binOp->getOperand(1);
  auto *Result = binOp;
  IRBuilder<> IRB(binOp->getNextNonDebugInstruction());
  bool isSub = binOp->getOpcode() == Instruction::Sub;
  bool isAdd = binOp->getOpcode() == Instruction::Add;
  if (!isSub && !isAdd)
    return;
  Value *typeStr = IRB.CreateGlobalStringPtr(isSub ? "SUB" : "ADD");

  Value *FormatStr =
      IRB.CreateGlobalStringPtr("BOP %s: %llx, %llx, result= %llx\n");
  PointerType *PtrTy = PointerType::getUnqual(M.getContext());

  IRB.CreateCall(printfFunc, {FormatStr, typeStr, Op0, Op1, Result});
}

PreservedAnalyses
FSanRewriteFunctionCallsPass::run(Module &M, ModuleAnalysisManager &MAM) {
  return PreservedAnalyses::all(); // BASTA PORCODIO
  bool changed = false;
  // if (!ClInstrumentHeap)
  //   return PreservedAnalyses::all();
  errs() << "[FSAN] Running FSanRewriteFunctionCallsPass on module: "
         << M.getName() << "\n";
  for (Function &F : M) {
    if (F.isDeclaration())
      continue;
    // Collect calls first to avoid iterator invalidation
    std::set<CallBase *> typedMallocLikeToRewrite;
    std::set<CallBase *> typedNewOperatorToRewrite;

    for (BasicBlock &BB : F) {
      for (Instruction &I : BB) {
        if (CallBase *CB = dyn_cast<CallBase>(&I)) {
          doQuickCheck(CB); // check that we did not miss this in FE
          if (isTypedMallocLike(CB)) {
            typedMallocLikeToRewrite.insert(CB);
          } // if isTypedMallocLike
          else if (isTypedNewOperator(CB)) {
            typedNewOperatorToRewrite.insert(CB);
          } // if isTypedNewOperator

        } // if CallBase
        {
          // DEBUG for other passes
          if (CmpInst *cmp = dyn_cast<CmpInst>(&I)) {
            if (ClInstrumentHeap)
              debugCMP(cmp, M);
          }
          if (BinaryOperator *binOp = dyn_cast<BinaryOperator>(&I)) {
            if (ClInstrumentHeap)
              debugBOP(binOp, M);
          }
        }
      } // for BB
    } // for

    for (CallBase *CI : typedMallocLikeToRewrite) {
      if (ClInstrumentHeap)
        changed |= ProcessMallocLikeCall(CI, M);
    }

    for (CallBase *CI : typedNewOperatorToRewrite) {
      if (ClInstrumentHeap)
        changed |= ProcessNewCall(CI, M);
    }
  }
  return (changed ? PreservedAnalyses::none() : PreservedAnalyses::all());
}

// --- Plugin registration (new pass manager) ---

llvm::PassPluginLibraryInfo getTypedAllocatorRewritePassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "FSanRewriteFunctionCallsPass",
          LLVM_VERSION_STRING, [](PassBuilder &PB) {
            // Register as a module pass so we can call
            // getOrInsertFunction on Module
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "FSanRewriteFunctionCalls") {
                    MPM.addPass(FSanRewriteFunctionCallsPass());
                    return true;
                  }
                  return false;
                });

            // Optionally run early in the optimization pipeline
            PB.registerPipelineStartEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel) {
                  MPM.addPass(FSanRewriteFunctionCallsPass());
                });
          }};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getTypedAllocatorRewritePassPluginInfo();
}