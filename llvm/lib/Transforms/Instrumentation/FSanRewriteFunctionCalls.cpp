#include "llvm/Transforms/Instrumentation/FSanRewriteFunctionCalls.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/Attributes.h"
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
#include <cstdint>
#include <deque>
#include <sys/types.h>

using namespace llvm;
#include "llvm/ADT/Statistic.h"
// number of tagged chunks
#define DEBUG_TYPE "fsan"
STATISTIC(NumCallsRewritten, "Number of function calls rewritten");

static cl::opt<bool> ClInstrumentHeap("fsan-instrument-heap",
                                      cl::desc("instrument heap"), cl::Hidden,
                                      cl::init(true));

// TODO: turn these into ct llvm flags
bool tagNew = true;
bool tagMallocLike = true;

bool FSanRewriteFunctionCallsPass::isTypedMallocLike(CallBase *CB) {
  Value *V = CB->getCalledOperand()->stripPointerCasts();
  Function *Callee = dyn_cast<Function>(V);
  auto demangledName = Callee ? llvm::demangle(Callee->getName().str()) : "";
  return (Callee &&
          demangledName == "typed_allocation"); // label for typed fnctn
}
bool FSanRewriteFunctionCallsPass::isTypedNewOperator(CallBase *CB) {
  Value *V = CB->getCalledOperand()->stripPointerCasts();
  Function *Callee = dyn_cast<Function>(V);
  auto demangledName = Callee ? llvm::demangle(Callee->getName().str()) : "";
  return (Callee && demangledName.find("operator new") !=
                        std::string::npos); // for now, TODO later fix
}

bool doCheckOnCookie(Value *V) {
  // errs() << "[IR] CHECKING COOKIE on ";
  // V->dump();
  // example @COOKIE_IS_THERE.9 = private unnamed_addr constant [13 x i8]
  // c"PINO_PALETTA\00", align 4
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

// TODO: write rewriteNewLike
// TODO: handle array sizes for news
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
  // errs() << "Rewriting call to " << formerAllocatorName << "\n";
  // CI->dump();

  // inline std::set<std::string> allocFunctions = {
  //     "malloc",        "realloc",        "calloc", "reallocarray",
  //     "memalign", "aligned_alloc", "posix_memalign", "valloc", "pvalloc"};
  // extract size, n, former ptr
  if (formerAllocatorName == "malloc") {
    allocSize = CI->getArgOperand(0);
  } // malloc
  else if (formerAllocatorName == "realloc") {
    origPtr = CI->getArgOperand(0);
    allocSize = CI->getArgOperand(1);
    isRealloc = true;
  } // realloc
  else if (formerAllocatorName == "calloc") {
    allocSize = CI->getArgOperand(0);
    nElems = CI->getArgOperand(1);
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
      // DBG dump old function type
      // errs() << "[IR-DBG] Old invoked function type: " << *OldInvokedFuncTy
      //        << "\n";
      // errs() << "Old invoked function " << *OldInvokedFunc << "\n";
      // errs() << "Arguments size " << arguments.size() << "\n";
      // for (auto arg : arguments) {
      //   arg->dump();
      // }
      // TODO: enforce the signature of the new operator is correct
      InvokeInst *NewInvoke =
          InvokeInst::Create(OldInvokedFuncTy, OldInv->getCalledOperand(), Dest,
                             UnwindDest, arguments, "invoke.rewrite");
      // TODO: REFACTOR and fix attributes to function call to match
      // original!
      // NewInvoke->dump();
      NewInvoke->setDebugLoc(OldInv->getDebugLoc());
      // NewInvoke->setTailCall(true);

      // OldInv->dump();
      // Insert it before the old one
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
      // CI->dump();

      CallInst *NewCall = CallInst::Create(
          NewOperatorTy, CI->getCalledOperand(), arguments, "call.rewrite");
      NewCall->setTailCall(true);
      NewCall->setDebugLoc(CI->getDebugLoc());

      NewCall->insertBefore(CI);
      // NewCall->dump();
      CI->replaceAllUsesWith(NewCall);
      CI->eraseFromParent();
      return NewCall;
    }

    return nullptr;
  } // if isNew

  IRBuilder<> IRB(CI);
  // errs() << "[IR] MALLOC-LIKE FORMER FUNCTION SIGNATURE: "
  //        << *formerFn.getCallee() << "\n";

  CallBase *formerCall = IRB.CreateCall(formerFn, arguments);
  // TODO: REFACTOR and fix attributes
  // formerCall->addParamAttr(0, Attribute::NoAlias);
  // if (isRealloc)
  //   formerCall->addParamAttr(1, Attribute::None); // size
  // formerCall->addRetAttr(Attribute::NoAlias);
  // formerCall->addParamAttr(0, Attribute::get(Ctx, "noundef"));
  // if (isRealloc)
  //   formerCall->addParamAttr(1, Attribute::get(Ctx, "noundef"));

  // formerCall->setCallingConv(CallingConv::C);
  CI->replaceAllUsesWith(formerCall);
  CI->eraseFromParent();
  NumCallsRewritten++;
  return formerCall;
}

Value *GetArraySize(CallBase *CI, std::string demangledName, Module &M,
                    StructType *t, IRBuilder<> &IRB) {
  assert(!demangledName.empty() && "Demangled name cannot be empty");
  uint64_t typeSize = M.getDataLayout().getTypeAllocSize(t);

  if (typeSize == 0)
    return nullptr;
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

/** prototype */
uint8_t *computeTags(StructType *Ty, Module &M);
GlobalVariable *retrieveTV(StructType *Ty, Module &M);

u_int8_t *computeTags(StructType *Ty, Module &M) {
  DataLayout DL = M.getDataLayout();
  uint8_t *tags = new uint8_t[DL.getTypeAllocSize(Ty)];
  memset(tags, 0xff, DL.getTypeAllocSize(Ty));

  assert(tags && "Could not allocate tags array");
  std::deque<std::tuple<Type *, uint8_t, uint8_t, uint8_t, size_t>> AggQueue;
  auto levelZeroFieldsOffsets = DL.getStructLayout(Ty)->getMemberOffsets();

  uint8_t fatherT = 0;
  uint8_t fatherL = 0;
  uint16_t sonIdx = 1;
  if (levelZeroFieldsOffsets.size() >= (1 << 16) - 1)
    return nullptr;

  for (auto subtype : Ty->subtypes()) {
    AggQueue.push_back(std::make_tuple(subtype, fatherT, fatherL, sonIdx,
                                       levelZeroFieldsOffsets[sonIdx - 1]));
    sonIdx++;
  }

  while (!AggQueue.empty()) {

    auto el_pair = AggQueue.front();
    AggQueue.pop_front();
    Type *sonType = std::get<0>(el_pair);
    fatherT = std::get<1>(el_pair);
    fatherL = std::get<2>(el_pair);
    sonIdx = std::get<3>(el_pair);
    size_t sonOffset = std::get<4>(el_pair);

    auto ST_son = dyn_cast<StructType>(sonType);
    auto isLitStr = ST_son && ST_son->isLiteral();

    auto isUnion =
        ST_son && !isLitStr && (ST_son->getName().find("union.") == 0);

    if (ST_son && !isLitStr && !isUnion) {
      u_int8_t newBaseTag = 0; // FLAT scheme introduced here
      uint8_t count = 0;
      auto sonSubfieldsCount = sonType->getNumContainedTypes();

      auto sonSubfieldsOffsets =
          DL.getStructLayout(cast<StructType>(sonType))->getMemberOffsets();
      size_t currSonSubfieldOffset = 0;

      for (Type *subtype : llvm::reverse(sonType->subtypes())) {
        currSonSubfieldOffset =
            sonSubfieldsOffsets[sonSubfieldsCount - count - 1] + sonOffset;
        AggQueue.push_front(
            std::make_tuple(subtype, newBaseTag, (fatherL + 1) % 4,
                            sonSubfieldsCount - count, currSonSubfieldOffset));
        count++;
      } // for subtype
    } // if son struct

    else if (sonType->isArrayTy()) {
      Type *elementType = sonType->getArrayElementType();
      if (elementType->isStructTy()) {
        // case : ARRAY of STRUCTS embedded in a struct
        if (StructType *structType = dyn_cast<StructType>(elementType)) {
          if (structType->isLiteral()) {

            // dont tag literal structs arrays for now
            continue;
          } else if (structType->getName().str().find("union.") == 0) {
            // dont tag union arrays for now
            continue;
          }
        } // skip literal and unions

        auto structType = cast<StructType>(elementType);
        auto structName = structType->getStructName().str();

        GlobalVariable *tagVectorGlobal =
            dyn_cast<GlobalVariable>(retrieveTV(structType, M));
        if (!tagVectorGlobal)
          continue;

        Constant *tagVectorInit =
            cast<Constant>(tagVectorGlobal->getInitializer());

        uint64_t elementSize = DL.getTypeAllocSize(elementType);
        uint64_t arraySize = DL.getTypeAllocSize(sonType);
        uint64_t numElements = arraySize / elementSize;

        for (u_int64_t k = 0; k < numElements; k++) {
          uint64_t elemOffset = sonOffset + k * elementSize;
          for (u_int64_t i = 0; i < elementSize; i++) {
            tags[elemOffset + i] = static_cast<uint8_t>(
                cast<ConstantInt>(tagVectorInit->getAggregateElement(i))
                    ->getZExtValue());
          }
        } // for each struct, copy its tag vector at the right position
      } // case: array of structs embedded in a struct

      else if (elementType->isArrayTy()) {
        auto innerArrayType = dyn_cast<ArrayType>(elementType);
        Type *innerElementType = innerArrayType->getArrayElementType();
        if (innerElementType->isStructTy()) {
          // case : matrix of structs
          auto structType = cast<StructType>(innerElementType);
          if (structType->isLiteral()) {
            // dont tag literal struct matrices for now
            continue;
          } else if (structType->getName().str().find("union.") == 0) {
            // dont tag union matrices for now
            continue;
          }

          // TODO: handle arrays of C++ classes. What happens if the wrong
          // tag vector is used? E.g. base vs non-base? Using struct size
          // should be fine though.

          auto structName = structType->getStructName().str();
          GlobalVariable *tagVectorGlobal = retrieveTV(structType, M);

          auto sizeOuterArray = DL.getTypeAllocSize(sonType);
          auto sizeInnerArray = DL.getTypeAllocSize(elementType);
          uint64_t numOuterElements = sizeOuterArray / sizeInnerArray;
          uint64_t structSize = DL.getTypeAllocSize(innerElementType);
          uint64_t numInnerElements = sizeInnerArray / structSize;
          Constant *tagVectorInit =
              cast<Constant>(tagVectorGlobal->getInitializer());

          for (u_int64_t k = 0; k < numOuterElements; k++) {
            // each element is an array of structs
            uint64_t currOuterArrayOffset = sonOffset + k * sizeInnerArray;

            for (u_int64_t h = 0; h < numInnerElements; h++) {
              uint64_t currInnerArrayOffset =
                  currOuterArrayOffset + h * structSize;
              for (u_int64_t i = 0; i < structSize; i++) {
                tags[currInnerArrayOffset + i] = static_cast<uint8_t>(
                    cast<ConstantInt>(tagVectorInit->getAggregateElement(i))
                        ->getZExtValue());
              } // for each byte of the tag vector of the struct
            } // for each struct
          } // for each array of structs
        } // case : matrix of structs

        else {
          // array of arrays of scalars, or array of arrays of arrays of
          // something else -> all same tag
          // NOTE: this could be 3d matrices of structs as well!
          uint8_t sonT = (fatherT + sonIdx) % 16;
          uint8_t sonTag = sonT | (fatherL << 4);
          uint64_t sonSize = DL.getTypeAllocSize(sonType);
          for (uint64_t i = 0; i < sonSize; i++) {
            tags[sonOffset + i] = sonTag;
          }
        } // case: matrix of scalars/arrays
      } // case: inner element of array is an array
      else {
        // array of scalars -> all same tag
        uint8_t sonT = (fatherT + sonIdx) % 16;
        uint8_t sonTag = sonT | (fatherL << 4);
        uint64_t sonSize = DL.getTypeAllocSize(sonType);
        for (uint64_t i = 0; i < sonSize; i++) {
          tags[sonOffset + i] = sonTag;
        }
      } // array of scalars
    } // case: son is array

    else {
      // case : scalar fields, literal structs, unions == ALL SCALAR

      if (sonType->isStructTy()) {
        StructType *ty = dyn_cast<StructType>(sonType);

        memset(&tags[sonOffset], 0x00,
               DL.getTypeAllocSize(sonType)); // treat as NULL scalar field

      } else {
        // uint8_t sonT = (fatherT + sonIdx) % 16;
        // uint8_t sonTag = sonT | (fatherL << 4);
        // if (isUnion)
        //   sonTag = 0x00;
        int sonSize = DL.getTypeAllocSize(sonType);
        // for (int i = 0; i < sonSize; i++) {
        //   tags[sonOffset + i] = sonTag;
        // }
        // array of scalars -> all same tag
        uint8_t sonT = (fatherT + sonIdx) % 16;
        uint8_t sonTag = sonT | (fatherL << 4);
        uint64_t remainingSizeOfStruct = DL.getTypeAllocSize(Ty) - (sonOffset);
        // TODO: if size is 1 byte and field is the last field of the struct,
        // detect possible flexible array and memset remaining part of tagVector
        // to 0 to avoid FPs
        bool isLastFieldOfStruct =
            (sonIdx) ==
            Ty->getNumContainedTypes(); // NOTEL sonIdx is adj to be 1-based
        // if (isLastFieldOfStruct)
        //   errs() << "[FieldArmor] Detected possible flexible array of size 0
        //   "
        //             "at offset "
        //          << sonOffset << " of struct " << *Ty << ", sonSize " <<
        //          sonSize
        //          << "\n";
        if (sonSize == 1 && isLastFieldOfStruct) {
          // errs() << "[FieldArmor] Detected possible flexible array at offset
          // "
          //        << sonOffset << " of struct " << *Ty << ", memsetting "
          //        << remainingSizeOfStruct << " bytes to 0\n";
          // detect possible flexible array and memset remaining part of
          // tagVector to 0 to avoid FPs
          memset(&tags[sonOffset], 0x00, remainingSizeOfStruct);

        } else
          for (uint64_t i = 0; i < sonSize; i++)
            tags[sonOffset + i] = sonTag;
      }
    } // case : scalar fields, literal structs, unions
  } // while agg queue not empty

  return tags;
} // computeTags

GlobalVariable *retrieveTV(StructType *t, Module &M) {
  std::string TagVecName = t->getStructName().str() + ".fieldarmor.tagvec";
  auto *TagVec = M.getGlobalVariable(TagVecName, true);
  if (TagVec)
    return TagVec;

  auto size = M.getDataLayout().getTypeAllocSize(t);

  u_int8_t *tags = nullptr;
  bool isLiteral = t->isLiteral();

  bool isUnion =
      !isLiteral && t->getName().str().find("union.") != std::string::npos;

  // TODO: do literals exist in this case? I think they are never on the heap!
  if (isLiteral || isUnion) {
    tags = new uint8_t[size];
    memset(tags, (unsigned char)0x00, size);
  } else {
    tags = computeTags(t, M);
  }
  auto Int8Ty = Type::getInt8Ty(M.getContext());
  ArrayType *TagArrayType = ArrayType::get(Int8Ty, size);
  std::vector<llvm::Constant *> Elements(size,
                                         llvm::ConstantInt::get(Int8Ty, 0));
  for (unsigned long i = 0; i < size; i++) {
    Elements[i] = llvm::ConstantInt::get(Int8Ty, tags[i]);
  }
  delete[] tags; // NOTE: is it responsibility of the caller to delete

  llvm::Constant *Init = llvm::ConstantArray::get(TagArrayType, Elements);
  auto *NewTagVector_global = new GlobalVariable(
      M, TagArrayType, true, GlobalVariable::PrivateLinkage, Init, TagVecName);
  NewTagVector_global->setSection("porcodiddio"); // is this necessary?
  return NewTagVector_global;
}

// TODO: reuse for the NEW as well
bool FSanRewriteFunctionCallsPass::RewriteCallToTypedAllocator(CallBase *CI,
                                                               Module &M) {
  // errs() << "\t[IR] REWRITING MALLOC-LIKE CALL: " << *CI << "\n";
  // errs() << "\t\t SRC LOCATION: ";
  // if (DILocation *Loc = CI->getDebugLoc()) {
  //   errs() << Loc->getFilename() << ":" << Loc->getLine() << "\n";
  // }
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
    // errs() << "\t\t[IR] Not enough arguments for typed allocator call, "
    //           "skipping.\n";
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

  if (!strPtr || !arraySize || !formerFunction) {
    errs() << "\t\t[IR] BUG : FAILED TO EXTRACT ARGS: " << "strPtr: "
           << (strPtr ? "present" : "null")
           << ", arraySize: " << (arraySize ? "present" : "null")
           << ", formerFunction: " << (formerFunction ? "present" : "null")
           << "\n";
    CI->dump();
    assert(false &&
           "Failed to extract necessary arguments for typed allocator call");
  }

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
          // llvm::errs() << "\t[DBG-IR] STRUCT TYPE: "
          //              << allocType->getStructName() << "\n";
          dontTag = false;
        } // it's struct or class
        else {
          if (structName.find("union") != std::string::npos) {
            // errs() << "\t[DBG-IR] UNION TYPE IDENTIFIED: " << structName
            //        << "\n";
            dontTag = true;
          } else {
            // llvm::errs() << "\t[DBG-IR] NOT A STRUCT/CLASS/UNION: "
            //              << structName << "\n";
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
        // llvm::errs() << "[DBG-IR] FUNCTION TO CALL: " << formerAllocatorName
        //              << "\n";
      }
    }
  }
  // llvm::errs() << "[DBG-IR] ARRAY SIZE: " << *arraySize << "\n";

  // this is a destructive operation for CI
  CallBase *formerCall =
      rewriteCall(CI, allocType, arraySize, formerAllocatorName, M);
  assert(formerCall &&
         "Failed to rewrite malloc-like call to former allocator");

  CallInst *newCI = dyn_cast<CallInst>(formerCall);
  assert(newCI && "Expected the rewritten call to be an instruction");
  newCI->setName(CI->getName() + ".fieldarmor.rewrite");
  bool changed = true;

  // errs() << "\t[IR] REWRITING OK: " << *newCI << "\n";
  if (allocType && !dontTag && ClInstrumentHeap) {
    IRBuilder<> IRB(newCI->getNextNonDebugInstruction());

    Value *ArraySize =
        GetArraySize(newCI, formerAllocatorName, M, allocType, IRB);
    assert(ArraySize != nullptr &&
           "Failed to compute array size for typed allocation");
    TypeSize tSize = M.getDataLayout().getTypeAllocSize(allocType);
    // now tag with tagging function
    FunctionCallee fieldarmor_tag_memory =
        M.getOrInsertFunction("_ZN8__hwasan21fieldarmor_tag_memoryEPvmm", PtrTy,
                              PtrTy, PtrTy, Int64Ty, Int64Ty);
    assert(fieldarmor_tag_memory &&
           "Expected to find or insert fieldarmor_tag_memory function");
    auto *TagVector = retrieveTV(allocType, M);
    assert(TagVector &&
           "Failed to retrieve or create tag vector for struct type");
    IRB.CreateCall(fieldarmor_tag_memory,
                   {IRB.CreatePointerCast(newCI, PtrTy),
                    IRB.CreatePointerCast(TagVector, PtrTy),
                    ConstantInt::get(Int64Ty, tSize), ArraySize});
    // llvm::errs() << "[FieldArmor] DYNAMIC TAGGING SUCCESS on
    // malloc-like:\n\t"
    //              << *newCI
    //              << "\n\t\tstruct type: " << allocType->getStructName()
    //              << "\n\t\tARRAY SIZE: " << *ArraySize << "\n";
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
          // llvm::errs() << "\tINVOKE USR: " << demangledNameOfInvoke << "\n";
        }
      }
    }
  }
}

bool processNewOperatorCalls(CallBase *I, Module &M) {
  // NOTE on sizing news -> cookie!!!!!
  Value *V = I->getCalledOperand()->stripPointerCasts();
  bool changed = false;
  Function *Callee = dyn_cast<Function>(V);
  if (Callee) {
    StringRef name = Callee->getName();
    std::string demangledName = demangle(Callee->getName().str());
    // at this point, this must be true
    if (demangledName.find("operator new") != std::string::npos) {
      // llvm::errs() << "[IR] CALL/INVOKE NEW: " << demangledName << ", " << *I
      //              << "\n";
      // dbgSrcAndUses(I); // dump src and invoke uses => CONSTRUCTORS
      // doQuickCheckOnMD(I); // check if MD is there, just for comparison
      { // NO THROW CASE
        // skip on throw for now
        if (demangledName.find("nothrow") != std::string::npos) {
          // llvm::errs() << "\t\t[IR] NOTHROW NEW, skipping for now\n";
          return false;
        }
      } // NO THROW CASE

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
            // llvm::errs() << "\t\t[IR-DBG] LAST PARAM DUMP: " << structName
            //              << "\n";
            // NOTE: right now, placement news are not handled because
            // their type is a placeholder string. TODO: future work.
            if (allocType = StructType::getTypeByName(Callee->getContext(),
                                                      structName)) {
              // llvm::errs() << "\t\t[IR] LAST PARAM IS STRUCT: " << structName
              //              << "\n";
            }
          } else {

            // llvm::errs() << "\t\t[IR-DBG] LAST PARAM IS NOT STRING: "
            //              << *lastArg << "\n";
            auto *type = lastArg->getType();
            // llvm::errs() << "\t\t[IR-DBG] LAST PARAM TYPE: " << *type <<
            // "\n";
            if (PHINode *phi = dyn_cast<PHINode>(lastArg)) {
              // llvm::errs() << "\t\t[IR-DBG] LAST PARAM IS PHI NODE, dumping "
              //                 "incoming values:\n";
              // for (unsigned i = 0; i < phi->getNumIncomingValues(); i++) {
              //   Value *incoming = phi->getIncomingValue(i);
              //   // llvm::errs() << "\t\t\tINCOMING VALUE: " << *incoming <<
              //   "\n";
              // }
              auto *name = phi->getIncomingValue(0);
              if (Constant *nameConst = dyn_cast<Constant>(name)) {
                if (ConstantDataArray *dataArray =
                        dyn_cast<ConstantDataArray>(nameConst->getOperand(0))) {
                  if (dataArray->isString()) {
                    StringRef structNameRef = dataArray->getAsString();
                    std::string structName =
                        structNameRef.str().substr(0, structNameRef.size() - 1);
                    // llvm::errs() << "\t\t[IR-DBG] PHI NODE INCOMING VALUE IS
                    // "
                    //                 "STRING CONST: "
                    //              << structName << "\n";
                    if (allocType = StructType::getTypeByName(
                            Callee->getContext(), structName)) {
                      // llvm::errs()
                      //     << "\t\t[IR] LAST PARAM IS STRUCT: " << structName
                      //     << "\n";
                    }
                  }
                }
              }
            } else
              assert(false &&
                     "Expected last argument to be a string constant in "
                     "processNewOperatorCalls");
          }
        }
      } // if constant last arg
      // errs() << "\t\t[IR] REWRITING CALL TO NEW OPERATOR: " << *I << "\n";
      bool needsOffsetForCookie = false;
      CallBase *NewCI = rewriteCall(I, allocType, nullptr, demangledName, M,
                                    &needsOffsetForCookie);
      // errs() << "\t\t[IR] REWRITING OK: " << *NewCI << "\n";
      // if (needsOffsetForCookie) {
      //   errs() << "[IR] NEW OPERATOR CALL WITH COOKIE, will offset tagging by
      //   "
      //             "8 bytes\n";
      // }

      bool isUnion = (!structName.empty() &&
                      structName.find("union") != std::string::npos);
      if (isUnion) {
        // llvm::errs() << "\t\t[IR] UNION TYPE , SKIP: " << structName << "\n";
        return true; // we are not rewriting here!!!!
      }

      { // do the tagging
        if (allocType && allocType->isStructTy() && ClInstrumentHeap) {
          // llvm::errs() << "[FieldArmor] TYPE TO TAG: "
          //              << allocType->getStructName() << "\n";
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
            InsertPt =
                NewCI->getNextNonDebugInstruction(); // insert right after
                                                     // the new call
          assert(InsertPt && "Failed to find insertion point for tagging after "
                             "new operator call");
          // errs() << "\t\t[IR] INSERTION POINT FOR TAGGING: ";
          // InsertPt->dump();
          IRBuilder<> IRB(InsertPt);

          // TODO: check on array size post FP
          Value *ArraySize =
              GetArraySize(NewCI, demangledName, M, allocType, IRB);
          assert(ArraySize != nullptr &&
                 "Failed to compute array size for typed allocation");
          TypeSize tSize = M.getDataLayout().getTypeAllocSize(allocType);
          auto Int64Ty = Type::getInt64Ty(M.getContext());
          PointerType *PtrTy = PointerType::getUnqual(M.getContext());
          // errs() << "\t\t[IR] HERE - ARRAY SIZE: " << *ArraySize << "\n";
          FunctionCallee fieldarmor_tag_memory =
              M.getOrInsertFunction("_ZN8__hwasan21fieldarmor_tag_memoryEPvmm",
                                    PtrTy, PtrTy, PtrTy, Int64Ty, Int64Ty);
          assert(fieldarmor_tag_memory &&
                 "Expected to find or insert fieldarmor_tag_memory "
                 "function");
          auto *TagVector = retrieveTV(allocType, M);
          assert(TagVector &&
                 "Failed to retrieve or create tag vector for struct type");
          Value *whereToTagFrom = NewCI;
          bool isNewArray = demangledName.find("new[]") != std::string::npos;

          // TODO: whereToTagFrom is the ptr to the first eleme of the
          // array

          if (isNewArray && needsOffsetForCookie) {
            // errs() << "\t\t[IR] NEW[] WITH COOKIE, OFFSETTING TAGGING POINTER
            // "
            //           "BY 8 "
            //           "BYTES\n";
            Value *Offset =
                IRB.CreateGEP(IRB.getInt8Ty(), // element type: i8 (1 byte
                                               // per index unit)
                              NewCI,           // base pointer
                              IRB.getInt64(8), // offset by 8 bytes
                              "cookie_ptr");
            whereToTagFrom = Offset;
          }

          IRB.CreateCall(fieldarmor_tag_memory,
                         {IRB.CreatePointerCast(whereToTagFrom, PtrTy),
                          IRB.CreatePointerCast(TagVector, PtrTy),
                          ConstantInt::get(Int64Ty, tSize), ArraySize});
          // llvm::errs() << "[FieldArmor] DYNAMIC TAGGING SUCCESS on new:\n\t"
          //              << *NewCI
          //              << "\n\t\tstruct type: " << allocType->getStructName()
          //              << "\n\t\tARRAY SIZE: " << *ArraySize << "\n";
          NewCI->setName(NewCI->getName() + ".tagged");
          changed = true;
        } // if allocType
        else
          return changed;
      } // do the tagging
      // } // if allocType
    } // it's operator new
    else
      assert(false && "Expected operator new call in processNewOperatorCalls");
  } // if Callee
  else {
    assert(false && "Expected a function call in processNewOperatorCalls");
  }
  return changed;
} // processNewOperatorCalls

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
        // NOTE: "magic mallocs" appear when LLVM can infer the dst of an
        // indirect call and that is a malloc-like function.
        // Q: can we catch all the mallocs that randomly appear?
        // llvm::errs() << "[IR] MAGIC MALLOC ALERT : " << name
        //              << " (demangled: " << demangledName << ")\n";
        // CI->dump();

        // llvm::errs() << "\tNumber of uses: " << CI->getNumUses() << "\n";
        // if (CI->getNumUses() > 0) {
        //   // I expect something newly created to have a lot of uses
        //   llvm::errs() << "\tUsers:\n";
        //   for (User *U : CI->users()) {
        //     llvm::errs() << "\t\t" << *U << "\n";
        //   }
        // }
      }
    }
  }
}

PreservedAnalyses
FSanRewriteFunctionCallsPass::run(Module &M, ModuleAnalysisManager &MAM) {
  bool changed = false;
  llvm::errs() << "[IR] Running FSanRewriteFunctionCallsPass on module: "
               << M.getName() << "\n";
  llvm::errs() << "[FSAN] HEAP INSTRUMENTATION: " << (ClInstrumentHeap ? "ON" : "OFF")
               << "\n";
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
      } // for BB
    } // for

    for (CallBase *CI : typedMallocLikeToRewrite) {
      changed |= RewriteCallToTypedAllocator(CI, M);
    }

    for (CallBase *CI : typedNewOperatorToRewrite) {
      changed |= processNewOperatorCalls(CI, M);
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