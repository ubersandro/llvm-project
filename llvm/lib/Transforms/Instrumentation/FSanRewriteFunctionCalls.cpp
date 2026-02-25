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

// TODO: write rewriteNewLike
// TODO: handle array sizes for news
Value *rewriteCall(CallBase *CI, StructType *allocType, Value *arraySize,
                   const std::string &formerAllocatorName, Module &M) {
  bool isNew = false;
  Value *allocSize = nullptr;
  Value *nElems = nullptr;
  Value *origPtr = nullptr;
  LLVMContext &Ctx = M.getContext();
  Type *SizeTy = M.getDataLayout().getIntPtrType(Ctx); // use for size
  Type *VoidPtrTy = CI->getType();                     // opaque
  FunctionCallee formerFn;
  bool isRealloc = false;

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
  } // operator new[]
  else if (formerAllocatorName.find("operator new") != std::string::npos) {
    allocSize = CI->getArgOperand(0);
    isNew = true;
    arraySize = ConstantInt::get(SizeTy, 1);
  } // operator new

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
    // TODO : correct way of handling this is to push all the args, except the
    // last one! New operators have several overloads.
  }
  if (isNew)
    return nullptr;
  // if (isNew) {
  //   bool isInvoke = isa<InvokeInst>(CI);
  //   errs() << "DBG - rewrite NEW: " << *CI << "\n";

  //   auto *nextInstr = CI->getNextNonDebugInstruction();
  //   if (!nextInstr) {
  //     errs() << "[rewriteCall]NO NEXT: " << *CI << "\n";
  //     errs() << "<FUNCTION>\n";
  //     CI->getFunction()->dump();
  //     errs() << "</FUNCTION>\n";
  //     // TODO: handle this case
  //     return nullptr; // TODO: handle this case, maybe insert at end of
  //   } // no NextInstr

  //   IRBuilder<> IRB(CI);
  //   auto typeSize = M.getDataLayout().getTypeAllocSize(allocType);
  //   if (!arraySize)
  //     arraySize =
  //         IRB.CreateUDiv(allocSize, ConstantInt::get(sizeType, typeSize));

  //   auto *prevCalleeFn =
  //       dyn_cast<Function>(CI->getCalledOperand()->stripPointerCasts());
  //   assert(prevCalleeFn &&
  //          "Failed to get previous callee function for operator new");

  //   errs() << "[DBG] DUMP PREV CALLEE\n";
  //   prevCalleeFn->dump();
  //   // errs() << "\n";

  //   Value *newCI = nullptr;

  //   if (isInvoke) {
  //     // errs() << "\t\t[IR] INVOKE NEW TO REWRITE: " << *CI << "\n";
  //     // InvokeInst *OldInv = cast<InvokeInst>(CI);
  //     // auto Int64Ty = Type::getInt64Ty(M.getContext());
  //     // FunctionType *NewFTy = FunctionType::get(
  //     //     VoidPtrTy, {Int64Ty}, false); // same sign for new and new[]
  //     // StringRef formerName = prevCalleeFn->getName();
  //     // Value *NewCallee = M.getOrInsertFunction(formerName,
  //     // NewFTy).getCallee(); assert(NewCallee && "Failed to get or insert
  //     new
  //     // operator function");
  //     // // NewCallee->dump();

  //     // SmallVector<Value *, 2> NewArgs{
  //     //     OldInv->getArgOperand(0)}; // Only size, skip typeName
  //     // // TODO: check on other types of invoke instructions
  //     // // https://llvm.org/doxygen/classllvm_1_1IRBuilderBase.html
  //     // InvokeInst *NewInv =
  //     //     IRB.CreateInvoke(NewFTy, NewCallee, OldInv->getNormalDest(),
  //     //                      OldInv->getUnwindDest(), NewArgs,
  //     //                      OldInv->getName());

  //     // // Copy attributes like noalias noundef nonnull #21
  //     // NewInv->setAttributes(OldInv->getAttributes());
  //     // NewInv->setCallingConv(OldInv->getCallingConv());
  //     // NewInv->setDebugLoc(OldInv->getDebugLoc());

  //     // // Replace uses & erase
  //     // llvm::errs() << "Replacing old invoke: " << *OldInv
  //     //              << " with new invoke: " << *NewInv << "\n";
  //     // OldInv->replaceAllUsesWith(NewInv);
  //     // OldInv->eraseFromParent();
  //     // newCI = NewInv;

  //   } else {
  //     // errs() << "\t\t[IR] CALL TO NEW TO REWRITE: " << *CI << "\n";
  //     // rewrite call as with malloc
  //   }

  //   return newCI;

  // } // if isNew
  // else {
  // malloc-like case, just rewrite call with new function and arguments
  IRBuilder<> IRB(CI);
  errs() << "[IR] MALLOC-LIKE FORMER FUNCTION SIGNATURE: "
         << *formerFn.getCallee() << "\n";

  CallBase *formerCall = IRB.CreateCall(formerFn, arguments);
  // formerCall->addParamAttr(0, Attribute::NoAlias);
  // if (isRealloc)
  //   formerCall->addParamAttr(1, Attribute::None); // size
  // formerCall->addRetAttr(Attribute::NoAlias);
  // formerCall->addParamAttr(0, Attribute::get(Ctx, "noundef"));
  // if (isRealloc)
  //   formerCall->addParamAttr(1, Attribute::get(Ctx, "noundef"));

  formerCall->setCallingConv(CallingConv::C);

  errs() << "[IR] Basic Block BEFORE:\n";
  CI->getParent()->dump();

  CI->replaceAllUsesWith(formerCall);
  CI->eraseFromParent();
  errs() << "[IR] Basic Block after erasing original call:\n";
  // CI->getParent()->dump();
  formerCall->getParent()->dump();
  
  return formerCall;
  // } // !isNew
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
  memset(tags, 0, DL.getTypeAllocSize(Ty));

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

          // TODO: handle arrays of C++ classes. What happens if the wrong tag
          // vector is used? E.g. base vs non-base? Using struct size should
          // be fine though.

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
        uint8_t sonT = (fatherT + sonIdx) % 16;
        uint8_t sonTag = sonT | (fatherL << 4);
        if (isUnion)
          sonTag = 0x00;
        int sonSize = DL.getTypeAllocSize(sonType);
        for (int i = 0; i < sonSize; i++) {
          tags[sonOffset + i] = sonTag;
        }
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
  errs() << "\t[IR] REWRITING MALLOC-LIKE CALL: " << *CI << "\n";
  errs() << "\t\t SRC LOCATION: ";
  if (DILocation *Loc = CI->getDebugLoc()) {
    errs() << Loc->getFilename() << ":" << Loc->getLine() << "\n";
  }
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
    errs() << "\t\t[IR] Not enough arguments for typed allocator call, "
              "skipping.\n";
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
          llvm::errs() << "\t[DBG-IR] STRUCT TYPE: "
                       << allocType->getStructName() << "\n";
          dontTag = false;
        } // it's struct or class
        else {
          if (structName.find("union") != std::string::npos) {
            errs() << "\t[DBG-IR] UNION TYPE IDENTIFIED: " << structName
                   << "\n";
            dontTag = true;
          } else {
            llvm::errs() << "\t[DBG-IR] NOT A STRUCT/CLASS/UNION: "
                         << structName << "\n";
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
        llvm::errs() << "[DBG-IR] FUNCTION TO CALL: " << formerAllocatorName
                     << "\n";
      }
    }
  }
  llvm::errs() << "[DBG-IR] ARRAY SIZE: " << *arraySize << "\n";

  // this is a destructive operation for CI
  Value *formerCall =
      rewriteCall(CI, allocType, arraySize, formerAllocatorName, M);
  assert(formerCall &&
         "Failed to rewrite malloc-like call to former allocator");

  CallInst *newCI = dyn_cast<CallInst>(formerCall);
  assert(newCI && "Expected the rewritten call to be an instruction");
  newCI->setName(CI->getName() + ".fieldarmor.rewrite");
  bool changed = true;

  errs() << "\t[IR] REWRITING OK: " << *newCI << "\n";
  if (allocType && !dontTag) {
    // DO THE TAGGING
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
    llvm::errs() << "[FieldArmor] DYNAMIC TAGGING SUCCESS on malloc-like:\n\t"
                 << *newCI
                 << "\n\t\tstruct type: " << allocType->getStructName()
                 << "\n\t\tARRAY SIZE: " << *ArraySize << "\n";
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
          llvm::errs() << "\tINVOKE USR: " << demangledNameOfInvoke << "\n";
        }
      }
    }
  }
}

bool processNewOperatorCalls(CallBase *I, Module &M) {

  Value *V = I->getCalledOperand()->stripPointerCasts();
  bool changed = false;
  Function *Callee = dyn_cast<Function>(V);
  if (Callee) {
    StringRef name = Callee->getName();
    std::string demangledName = demangle(Callee->getName().str());
    // at this point, this must be true
    if (demangledName.find("operator new") != std::string::npos) {
      llvm::errs() << "[IR] CALL/INVOKE NEW: " << demangledName << ", " << *I
                   << "\n";
      // dbgSrcAndUses(I);
      // doQuickCheckOnMD(I);
      { // NO THROW CASE
        // skip on throw for now
        if (demangledName.find("nothrow") != std::string::npos) {
          llvm::errs() << "\t\t[IR] NOTHROW NEW, skipping for now\n";
          return false;
        }
      } // NO THROW CASE

      auto size = I->arg_size();
      auto lastArg = I->getArgOperand(I->arg_size() - 1); // typeName
      std::string structName = "";
      StructType *allocType;
      if (Constant *name = dyn_cast<Constant>(lastArg)) {
        if (ConstantDataArray *dataArray =
                dyn_cast<ConstantDataArray>(name->getOperand(0))) {
          if (dataArray->isString()) {
            StringRef structNameRef = dataArray->getAsString();
            std::string structName =
                structNameRef.str().substr(0, structNameRef.size() - 1);
            llvm::errs() << "\t\t[IR-DBG] LAST PARAM DUMP: " << structName
                         << "\n";
            // NOTE: right now, placement news are not handled because their
            // type is a placeholder string. TODO: future work.
            if (allocType = StructType::getTypeByName(Callee->getContext(),
                                                      structName)) {
              llvm::errs() << "\t\t[IR] LAST PARAM IS STRUCT: " << structName
                           << "\n";
            }
          } else
            assert(false && "Expected last argument to be a string constant in "
                            "processNewOperatorCalls");
        }
      } // if constant last arg
      if (allocType) {
        bool isUnion = (structName.find("union") != std::string::npos);
        if (isUnion) {
          llvm::errs() << "\t\t[IR] UNION TYPE , SKIP: " << structName << "\n";
          return false; // we are not rewriting here!!!!
        }
        // auto NewCI = rewriteCall(I, allocType, nullptr, demangledName, M);
        // NOTE: dead argument elimination is doing us a favor, ignore the above
        { // do the tagging
          if (allocType && allocType->isStructTy()) {
            // DO THE TAGGING
            llvm::errs() << "[FieldArmor] TYPE TO TAG: "
                         << allocType->getStructName() << "\n";
            Instruction *next = I->getNextNonDebugInstruction();
            IRBuilder<> IRB(I);

            if (next)
              IRB.SetInsertPoint(next);
            else {
              if (InvokeInst *II = dyn_cast<InvokeInst>(I)) {
                IRB.SetInsertPoint(II->getNormalDest()->getFirstNonPHI());
              } else
                assert(false && "Expected a call or invoke instruction in "
                                "processNewOperatorCalls");
            }

            // TODO: check on array size post FP
            Value *ArraySize =
                GetArraySize(I, demangledName, M, allocType, IRB);
            assert(ArraySize != nullptr &&
                   "Failed to compute array size for typed allocation");
            TypeSize tSize = M.getDataLayout().getTypeAllocSize(allocType);
            auto Int64Ty = Type::getInt64Ty(M.getContext());
            PointerType *PtrTy = PointerType::getUnqual(M.getContext());
            FunctionCallee fieldarmor_tag_memory = M.getOrInsertFunction(
                "_ZN8__hwasan21fieldarmor_tag_memoryEPvmm", PtrTy, PtrTy, PtrTy,
                Int64Ty, Int64Ty);
            assert(fieldarmor_tag_memory &&
                   "Expected to find or insert fieldarmor_tag_memory function");
            auto *TagVector = retrieveTV(allocType, M);
            assert(TagVector &&
                   "Failed to retrieve or create tag vector for struct type");

            // TODO: fix alignment, it's fucked up when allocating C++ object arrays
            // TODO: dump params at runtime
            IRB.CreateCall(fieldarmor_tag_memory,
                           {IRB.CreatePointerCast(I, PtrTy),
                            IRB.CreatePointerCast(TagVector, PtrTy),
                            ConstantInt::get(Int64Ty, tSize), ArraySize});
            llvm::errs() << "[FieldArmor] DYNAMIC TAGGING SUCCESS on new:\n\t"
                         << *I
                         << "\n\t\tstruct type: " << allocType->getStructName()
                         << "\n\t\tARRAY SIZE: " << *ArraySize << "\n";
            I->setName(I->getName() + ".tagged");
            changed = true;
          } // if allocType
        } // do the tagging
      } // if allocType
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
// TODO: bring back
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
        llvm::errs() << "[IR] MAGIC MALLOC ALERT : " << name
                     << " (demangled: " << demangledName << ")\n";
        CI->dump();

        llvm::errs() << "\tNumber of uses: " << CI->getNumUses() << "\n";
        if (CI->getNumUses() > 0) {
          llvm::errs() << "\tUsers:\n";
          for (User *U : CI->users()) {
            llvm::errs() << "\t\t" << *U << "\n";
          }
        }
      }
    }
  }
}

PreservedAnalyses
FSanRewriteFunctionCallsPass::run(Module &M, ModuleAnalysisManager &MAM) {
  bool changed = false;
  llvm::errs() << "[IR] Running FSanRewriteFunctionCallsPass on module: "
               << M.getName() << "\n";

  for (Function &F : M) {
    if (F.isDeclaration())
      continue;
    // skip if function has attribute "fregna"
    if (F.hasFnAttribute("fregna")) {
      llvm::errs() << "[IR] Skipping function with fregna attribute: "
                   << F.getName() << "\n";
      continue;
    }
    // Collect calls first to avoid iterator invalidation
    // SmallVector<CallBase *, 1000> typedMallocLikeToRewrite;
    // SmallVector<CallBase *, 1000> typedNewOperatorToRewrite;
    std::set<CallBase *> typedMallocLikeToRewrite;
    std::set<CallBase *> typedNewOperatorToRewrite;

    for (BasicBlock &BB : F) {
      for (Instruction &I : BB) {
        if (CallBase *CB = dyn_cast<CallBase>(&I)) {
          // doQuickCheck(CB); // check that we did not miss this in FE
          // TODO: bring back doQuickCheck
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
    // for (CallBase *CI : typedMallocLikeToRewrite) {
    //   CI->eraseFromParent(); // TODO: check if this actually works! Some
    //                          // function might be left there as deadcode if not
    //                          // delete after. We dont want this dead code
    //                          // because it can change memory layout and lead to
    //                          // more memory consumption.
    // }

    for (CallBase *CI : typedNewOperatorToRewrite) {
      changed |= processNewOperatorCalls(CI, M);
    }
    // for (CallBase *CI : typedNewOperatorToRewrite) {
    //   CI->eraseFromParent();
    // }
  }
  return (changed ? PreservedAnalyses::none() : PreservedAnalyses::all());
}

// --- Plugin registration (new pass manager) ---

llvm::PassPluginLibraryInfo getTypedAllocatorRewritePassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "FSanRewriteFunctionCallsPass",
          LLVM_VERSION_STRING, [](PassBuilder &PB) {
            // Register as a module pass so we can call getOrInsertFunction on
            // Module
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