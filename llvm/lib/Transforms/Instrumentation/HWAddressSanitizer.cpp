//===- HWAddressSanitizer.cpp - memory access error detector --------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// This file is a part of HWAddressSanitizer, an address basic correctness
/// checker based on tagged addressing.
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Instrumentation/HWAddressSanitizer.h"
#include "llvm/BinaryFormat/ELF.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Instrumentation/RuntimeTaggingSupport.hpp"
#include <cstdint>
#include <fstream>
#include <set>
#include <sys/types.h>

#define TRANS_CONSTANT 0x400000000000ULL // 1<<46, 0x400000000000
#define OFFSET_MEM 0x1000ULL

static llvm::cl::opt<std::string> FilterFilePath(
    "hwasan-filter-file",
    llvm::cl::desc("File containing struct names to protect/ignore"),
    llvm::cl::Hidden, llvm::cl::init(""));
std::set<std::string> FilterSet;

using namespace llvm;
using namespace RuntimeTaggingSupport;

#define DEBUG_TYPE "hwasan"
const char kHwasanModuleCtorName[] = "hwasan.module_ctor";
const char kHwasanNoteName[] = "hwasan.note";
const char kHwasanInitName[] = "__hwasan_init";
const char kHwasanPersonalityThunkName[] = "__hwasan_personality_thunk";

const char kHwasanShadowMemoryDynamicAddress[] =
    "__hwasan_shadow_memory_dynamic_address";

static cl::opt<std::string>
    ClMemoryAccessCallbackPrefix("hwasan-memory-access-callback-prefix",
                                 cl::desc("Prefix for memory access callbacks"),
                                 cl::Hidden, cl::init("__hwasan_"));
static cl::opt<bool> ClFSAN_verbose("fsan-verbose",
                                    cl::desc("print out more info"), cl::Hidden,
                                    cl::init(false));

static cl::opt<bool> ClFSAN_stack("fsan-instrument-stack",
                                  cl::desc("instrument stack allocations"),
                                  cl::Hidden, cl::init(true));

static cl::opt<bool> ClFSAN_globals("fsan-instrument-globals",
                                    cl::desc("Instrument globals"), cl::Hidden,
                                    cl::init(true));
// TODO: for heap, see FSanRewrite...
static cl::opt<bool> ClFSAN_memAccesses("fsan-instrument-mem-accesses",
                                        cl::desc("instrument memory accesses"),
                                        cl::Hidden, cl::init(true));
static cl::opt<bool>
    ClFSAN_memAccessesInline("fsan-instrument-mem-accesses-inline",
                             cl::desc("instrument memory accesses"), cl::Hidden,
                             cl::init(false));
// NO MEM ACCESSES + NO BOP -> 510 crashes for SEGV

static cl::opt<bool> ClFSAN_heap("fsan-instrument-heap",
                                 cl::desc("instrument heap"), cl::Hidden,
                                 cl::init(true));

static cl::opt<bool>
    ClFSAN_tag_heap("fsan-tag-heap",
                    cl::desc("insert call to tagging function for heap"),
                    cl::Hidden, cl::init(true));

static cl::opt<bool> ClFSAN_memIntr("fsan-instrument-mem-intrinsics",
                                    cl::desc("instrument memory intrinsics"),
                                    cl::Hidden, cl::init(true));
// FSAN KNOBS
static cl::opt<bool> ClInstrumentWithCalls(
    "hwasan-instrument-with-calls",
    cl::desc("instrument reads and writes with callbacks"), cl::Hidden,
    cl::init(true));

static cl::opt<bool> ClInstrumentReads("hwasan-instrument-reads",
                                       cl::desc("instrument read instructions"),
                                       cl::Hidden, cl::init(true));
static cl::opt<bool> ClSkipUnnamedStructs(
    "fsan-skip-unnamed-structs",
    cl::desc("skip instrumentation of unnamed struct types"), cl::Hidden,
    cl::init(false));
// NOTE: Skipping unnamed structs might cause FPs.

static cl::opt<bool>
    ClInstrumentWrites("hwasan-instrument-writes",
                       cl::desc("instrument write instructions"), cl::Hidden,
                       cl::init(true));

static cl::opt<bool> ClInstrumentAtomics(
    "hwasan-instrument-atomics",
    cl::desc("instrument atomic instructions (rmw, cmpxchg)"), cl::Hidden,
    cl::init(true));

static cl::opt<bool> ClInstrumentByval("hwasan-instrument-byval",
                                       cl::desc("instrument byval arguments"),
                                       cl::Hidden,
                                       cl::init(true)); // TODO: look into this

static cl::opt<bool> ClRecover(
    "hwasan-recover", cl::desc("Enable recovery mode (continue-after-error)."),
    cl::Hidden, cl::init(false)); // TODO: extend this with ignore_pc a la ASAN

static cl::opt<bool>
    ClUseStackSafety("hwasan-use-stack-safety", cl::Hidden, cl::init(true),
                     cl::Hidden, cl::desc("Use Stack Safety analysis results"),
                     cl::Optional); // TODO: does this remove UB?

static cl::opt<size_t> ClMaxLifetimes(
    "hwasan-max-lifetimes-for-alloca", cl::Hidden, cl::init(3),
    cl::ReallyHidden,
    cl::desc("How many lifetime ends to handle for a single alloca."),
    cl::Optional);

static cl::opt<int> ClMatchAllTag(
    "hwasan-match-all-tag",
    cl::desc("don't report bad accesses via pointers with this tag"),
    cl::Hidden, cl::init(-1)); // TODO look into this, might come in very handy

static cl::opt<bool>
    ClEnableKhwasan("hwasan-kernel",
                    cl::desc("Enable KernelHWAddressSanitizer instrumentation"),
                    cl::Hidden, cl::init(false));

static cl::opt<uint64_t>
    ClMappingOffset("hwasan-mapping-offset",
                    cl::desc("HWASan shadow mapping offset [EXPERIMENTAL]"),
                    cl::Hidden);

static cl::opt<bool>
    ClFrameRecords("hwasan-with-frame-record",
                   cl::desc("Use ring buffer for stack allocations"),
                   cl::Hidden);
static cl::opt<bool>
    ClInstrumentLandingPads("hwasan-instrument-landing-pads",
                            cl::desc("instrument landing pads"), cl::Hidden,
                            cl::init(false));

static cl::opt<bool> ClInstrumentPersonalityFunctions(
    "hwasan-instrument-personality-functions",
    cl::desc("instrument personality functions"), cl::Hidden, cl::init(true));

static cl::opt<bool> ClKasanMemIntrinCallbackPrefix(
    "hwasan-kernel-mem-intrinsic-prefix",
    cl::desc("Use prefix for memory intrinsics in KASAN mode"), cl::Hidden,
    cl::init(false));

// FSAN KNOBS
static cl::opt<bool> ClFSAN_PtrTagging("fsan-instrument-ptr-tagging",
                                       cl::desc("instrument pointer tagging"),
                                       cl::Hidden, cl::init(true));
static cl::opt<bool>
    ClFSAN_GEP("fsan-instrument-geps",
               cl::desc("instrument getelementptr instructions"), cl::Hidden,
               cl::init(true));

static cl::opt<bool> ClFSAN_BOP("fsan-instrument-bops",
                                cl::desc("instrument binary op instructions"),
                                cl::Hidden, cl::init(true));

static cl::opt<bool> ClFSAN_CMP("fsan-instrument-cmp",
                                cl::desc("instrument compare instructions"),
                                cl::Hidden, cl::init(true));

using namespace OffsetPorcodidio;
static cl::opt<OffsetKind> ClMappingOffsetDynamic(
    "hwasan-mapping-offset-dynamic",
    cl::desc("HWASan shadow mapping dynamic offset location"), cl::Hidden,
    cl::values(clEnumValN(OffsetKind::kGlobal, "global", "Use global"),
               clEnumValN(OffsetKind::kIfunc, "ifunc", "Use ifunc global"),
               clEnumValN(OffsetKind::kTls, "tls", "Use TLS")));

STATISTIC(NumTotalFuncs, "Number of total funcs");
STATISTIC(NumInstrumentedFuncs, "Number of instrumented funcs");
STATISTIC(NumNoProfileSummaryFuncs, "Number of funcs without PS");
STATISTIC(LiteralStructs,
          "Number of literal structs encountered, doubly counted though");
STATISTIC(NumInstrumentedGEPs, "Number of instrumented GEP instructions");
STATISTIC(NumInstrumentedGlobals, "Number of instrumented global variables");
STATISTIC(NumDefinedTagVectors, "Number of defined tag vectors (same as the "
                                "number of totally identified struct types.)");
STATISTIC(NumInstrumentedCMPs, "Number of instrumented CMP instructions");
STATISTIC(NumInstrumentedMemAccesses, "Number of instrumented memory accesses");
STATISTIC(NumMemAccessesInlined, "Number of memory accesses inlined");
STATISTIC(NumMemAccessesNotInlined, "Number of memory accesses not inlined");
STATISTIC(NumInstrumentedIntrinsics, "Number of instrumented intrinsics");
// Mode for selecting how to insert frame record info into the stack ring
// buffer.

PreservedAnalyses HWAddressSanitizerPass::run(Module &M,
                                              ModuleAnalysisManager &MAM) {
  // Return early if nosanitize_hwaddress module flag is present for the module.
  if (checkIfAlreadyInstrumented(M, "nosanitize_hwaddress"))
    return PreservedAnalyses::all();
  const StackSafetyGlobalInfo *SSI = nullptr;
  // const Triple &TargetTriple = M.getTargetTriple();
  // if (shouldUseStackSafetyAnalysis(TargetTriple,
  // Options.DisableOptimization))
  if (FilterFilePath.getNumOccurrences() > 0) {
    std::ifstream filterFile(FilterFilePath);
    std::string line;
    while (std::getline(filterFile, line)) {
      FilterSet.insert(line);
      errs() << "FSAN: FILTER class/struct " << line << "\n";
    }
    errs() << "FSAN: Loaded " << FilterSet.size()
           << " struct names into the filter set.\n";
  }
  // TODO: this might introduce UB, potentially delete!
  SSI = &MAM.getResult<StackSafetyGlobalAnalysis>(M);

  HWAddressSanitizer HWASan(M, false, false, SSI);
  auto &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

  for (Function &F : M) {
    HWASan.sanitizeFunction(F, FAM);
  }

  PreservedAnalyses PA = PreservedAnalyses::none();
  // DominatorTreeAnalysis, PostDominatorTreeAnalysis, and LoopAnalysis
  // are incrementally updated throughout this pass whenever
  // SplitBlockAndInsertIfThen is called.
  PA.preserve<DominatorTreeAnalysis>();
  PA.preserve<PostDominatorTreeAnalysis>();
  PA.preserve<LoopAnalysis>();
  // GlobalsAA is considered stateless and does not get invalidated unless
  // explicitly invalidated; PreservedAnalyses::none() is not enough. Sanitizers
  // make changes that require GlobalsAA to be invalidated.
  PA.abandon<GlobalsAA>();
  return PA;
}
bool CheckOnCookie(Value *V) {
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

bool HWAddressSanitizer::RewriteMallocLikeCall(CallBase *CI) {
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
    errs() << "\t\t[FSAN] NOT ENOUGH ARGS FOR TYPED ALLOCATOR? " << *CI << "\n";
    assert(false && "Expected at least 3 arguments for typed allocator call");
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
          dontTag = true;
        }
      }
    }
  }

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

  CallBase *NewCI = RewriteCall(CI, arraySize, formerAllocatorName,
                                nullptr); // no offset for cookie
  assert(NewCI && "Expected the rewritten call to be an instruction");

  auto oldName = NewCI->hasName() ? NewCI->getName().str() : "noname";
  NewCI->setName(oldName + ".fieldarmor.rewrite");
  bool changed = true;

  if (allocType && !dontTag && !allocType->isOpaque() && ClFSAN_tag_heap) {
    auto *NextInst = NewCI->getNextNonDebugInstruction();
    Instruction *InsertPt = nullptr;
    BasicBlock *BB;

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
    while (InsertPt && isa<PHINode>(InsertPt))
      InsertPt = InsertPt->getNextNode();
    assert(InsertPt &&
           "Failed to find insertion point for tagging after malloc-like call");
    IRBuilder<> IRB(InsertPt);
    Value *ArraySize = nullptr;
    int32_t extractedArraySize = 0;
    if (ConstantInt *CInt = dyn_cast<ConstantInt>(arraySize)) {
      extractedArraySize = CInt->getZExtValue();
      if (extractedArraySize != -1)
        ArraySize = ConstantInt::get(Int64Ty, extractedArraySize);
      else
        ArraySize = GetArraySize(NewCI, formerAllocatorName, allocType, IRB);
    } else
      ArraySize = GetArraySize(NewCI, formerAllocatorName, allocType, IRB);
    assert(ArraySize != nullptr &&
           "Failed to compute array size for typed allocation");

    TypeSize tSize = M.getDataLayout().getTypeAllocSize(allocType);
    auto *TagVector =
        RuntimeTaggingSupport::RetrieveOrCreateTagVector(allocType, M);
    assert(TagVector &&
           "Failed to retrieve or create tag vector for struct type");

    IRB.CreateCall(FSANTaggingFunc,
                   {IRB.CreatePointerCast(NewCI, PtrTy),
                    IRB.CreatePointerCast(TagVector, PtrTy),
                    ConstantInt::get(Int64Ty, tSize), ArraySize});
    // TODO
    // Value *NewCILong = IRB.CreatePtrToInt(NewCI, IntptrTy);
    // Value *TaggedNewCI = tagPointer(IRB, NewCI->getType(), NewCILong,
    //                                 ConstantInt::get(IntptrTy, RPTag));
    // NewCI->replaceUsesWithIf(TaggedNewCI, [NewCI, NewCILong](const Use &U) {
    //   auto *User = U.getUser();
    //   bool isCallToFSANTagMemory =
    //       isa<CallInst>(User) && cast<CallInst>(User)->getCalledFunction() &&
    //       cast<CallInst>(User)->getCalledFunction()->hasName() &&
    //       cast<CallInst>(User)->getCalledFunction()->getName().str().find(
    //           "fsan_tag_memory") != std::string::npos;
    //   bool safe = !isa<LifetimeIntrinsic>(User);
    //   safe &= !isa<DbgInfoIntrinsic>(User);
    //   safe &= !isCallToFSANTagMemory;
    //   safe &= (User != NewCILong);
    //   return safe;
    // });

    if (ClFSAN_verbose)
      errs() << "\t\t[FSAN-PASS] malloc-like tag\n\t" << *NewCI
             << "\n\ttype: " << structName << "\n\tarray size: " << *ArraySize
             << "\n";
  }
  return changed;
} // RewriteMallocLikeCall

bool HWAddressSanitizer::RewriteNewCall(CallBase *I) {
  Value *V = I->getCalledOperand()->stripPointerCasts();
  bool changed = false;
  Function *Callee = dyn_cast<Function>(V);
  if (Callee) {
    assert(Callee->hasName() &&
           "Expected callee to have a name in RewriteNewCall");
    std::string AllocatorName = demangle(Callee->getName().str());

    if (AllocatorName.find("nothrow") != std::string::npos) {
      errs() << "\t\t[FSAN] NOTHROW NEW " << *I << ", TODO\n";
      return false;
    }

    { // DEBUG
      bool IsAlignmentAwareNew =
          AllocatorName.find("align_val_t") != std::string::npos;
      if (IsAlignmentAwareNew) {
        errs() << "\t\t[FSAN-REW] Alignment-aware " << *I << "\n";
      }
    } // DEBUG

    auto size = I->arg_size();
    // NOTE: args are expected to be strictly more than one, otherwise it means
    // this call was not rewritten

    if (size <= 1) {
      // TODO: where do these calls come from?
      errs() << "\t\t[FSAN] TOO FEW ARGS. CALL REWRITTEN? " << *I << ", TODO\n";
      return false;
    }

    bool cookieIsThere = CheckOnCookie(I->getArgOperand(size - 1));
    auto lastArg =
        cookieIsThere
            ? I->getArgOperand(I->arg_size() - 2)
            : I->getArgOperand(I->arg_size() - 1); // typeName or COOKIE!!!

    std::string structName = "";
    StructType *allocType = nullptr; // this will be null for unhandled cases

    if (Constant *name = dyn_cast<Constant>(lastArg)) {
      if (ConstantDataArray *dataArray =
              dyn_cast<ConstantDataArray>(name->getOperand(0))) {
        if (dataArray->isString()) {
          StringRef structNameRef = dataArray->getAsString();
          structName = structNameRef.str().substr(0, structNameRef.size() - 1);
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
                            "RewriteNewCall");
        }
      }
    } // if constant last arg

    bool needsOffsetForCookie = cookieIsThere;
    CallBase *NewCI =
        RewriteCall(I, nullptr, AllocatorName, &needsOffsetForCookie);
    bool isUnion =
        (!structName.empty() && structName.find("union") != std::string::npos);

    if (isUnion) {
      errs() << "\t\t[FSAN-REW] NOT TAGGING UNION " << *I << "\n";
      return true;
    }

    if (allocType && allocType->isStructTy() && !allocType->isOpaque() &&
        ClFSAN_tag_heap) {
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

      // iterate on instructions after InsertPt, reach first NON-PHI instruction
      // while (InsertPt && isa<PHINode>(InsertPt))
      //   InsertPt = InsertPt->getNextNode();
      PHINode* PHI = nullptr; 
      if(PHI = dyn_cast<PHINode> (InsertPt)) {
        // the PHI node must be instrumented una tantum
        errs() << "\t\t[FSAN] PHI node detected as insertion point: " << *PHI << "\n";
        bool AlreadyInstrumented = false;
        for(User * U: PHI->users()) {
          if(isa<CallInst>(U) && cast<CallInst>(U)->getCalledFunction() &&
             cast<CallInst>(U)->getCalledFunction()->hasName() &&
             cast<CallInst>(U)->getCalledFunction()->getName().str().find(
                 "fsan_tag_memory") != std::string::npos) {
            AlreadyInstrumented = true;
            break;
          }
        }
        if(AlreadyInstrumented) {
          errs() << "\t\t[FSAN] PHI node already instrumented, skipping tagging for new call: " << *PHI << "\n";
          return changed;
        }
        else{
          while(InsertPt && isa<PHINode>(InsertPt))
            InsertPt = InsertPt->getNextNode();
        }
      }
      errs() << "\t\t[FSAN] TAGGING "<< *NewCI << " at: " << *InsertPt << "\n";
      IRBuilder<> IRB(InsertPt);

      // TODO: check on array size post FP
      Value *ArraySize = GetArraySize(NewCI, AllocatorName, allocType, IRB);
      assert(ArraySize != nullptr &&
             "Failed to compute array size for typed allocation");
      TypeSize tSize = M.getDataLayout().getTypeAllocSize(allocType);
      auto *TagVector =
          RuntimeTaggingSupport::RetrieveOrCreateTagVector(allocType, M);
      assert(TagVector &&
             "Failed to retrieve or create tag vector for struct type");
      Value *whereToTagFrom = NewCI;
      if(PHI!= nullptr) {
        whereToTagFrom = PHI;
      }
      bool isNewArray = AllocatorName.find("new[]") != std::string::npos;
      Value *Offset = nullptr;

      if (isNewArray && needsOffsetForCookie) {
        Offset = IRB.CreateGEP(IRB.getInt8Ty(), // element type: i8 (1
                                                // byte per index unit)
                               NewCI,           // base pointer
                               IRB.getInt64(8), // offset by 8 bytes
                               "cookie_ptr");
        Offset->setName(NewCI->getName() + ".cookie_offset");
        whereToTagFrom = Offset;
        errs() << "\t\t[FSAN] new[] with cookie, tagging from offset pointer: "
               << *Offset << "\n";
      }

      // NOTE: tagged pointer coming out of this could be offset by 8, cannot be
      // replaced as a drop in replacement with the original new operator call
      IRB.CreateCall(FSANTaggingFunc,
                     {IRB.CreatePointerCast(whereToTagFrom, PtrTy),
                      IRB.CreatePointerCast(TagVector, PtrTy),
                      ConstantInt::get(Int64Ty, tSize), ArraySize});

      if (ClFSAN_verbose)
        errs() << "\t\t[FSAN] new operator tag\n\t" << *NewCI
               << "\n\ttype: " << structName << "\n\tarray size: " << *ArraySize
               << "\n";
      changed = true;
    } // if allocType
    else
      return changed;

  } // if Callee
  else {
    assert(false && "Expected a function call in RewriteNewCall");
  }
  return changed;
} // RewriteNewCall

CallBase *
HWAddressSanitizer::RewriteCall(CallBase *CI, Value *arraySize,
                                const std::string &formerAllocatorName,
                                bool *needsOffsetForCookie) {
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
      hasAlignment = true;
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
    cookieStrIsThere = CheckOnCookie(CI->getArgOperand(CI->arg_size() - 1));
    if (cookieStrIsThere)
      errs() << "COOKIE ACK IN IR\n";
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
  return formerCall;
} // RewriteCall

Value *HWAddressSanitizer::GetArraySize(CallBase *CI, std::string demangledName,
                                        StructType *t, IRBuilder<> &IRB) {
  assert(!demangledName.empty() && "Demangled name cannot be empty");
  uint64_t typeSize = M.getDataLayout().getTypeAllocSize(t);

  if (typeSize == 0) {
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
  Value *Ret = nullptr;

  if (demangledName == "malloc" || demangledName == "valloc" ||
      demangledName == "pvalloc") {
    Value *MallocSizeValue = IRB.CreateZExt(CI->getArgOperand(0), Int64Ty);
    // return IRB.CreateUDiv(MallocSizeValue, TypeSizeValue);
    Ret = IRB.CreateUDiv(MallocSizeValue, TypeSizeValue);
  } else if (demangledName == "calloc") {
    Ret = IRB.CreateZExt(CI->getArgOperand(0), Int64Ty);
  } else if (demangledName == "realloc") {
    Value *ReallocSizeValue = IRB.CreateZExt(CI->getArgOperand(1), Int64Ty);
    Ret = IRB.CreateUDiv(ReallocSizeValue, TypeSizeValue);
  } else if (demangledName == "reallocarray") {
    Ret = IRB.CreateZExt(CI->getArgOperand(1), Int64Ty);
  } else if (demangledName.find("operator new") != std::string::npos) {
    bool isArrayNew = (demangledName.find("new[]") != std::string::npos);
    Value *NewSizeValue = IRB.CreateZExt(CI->getArgOperand(0), Int64Ty);
    if (isArrayNew) {
      Ret = IRB.CreateUDiv(NewSizeValue, TypeSizeValue);
    } else {
      Ret = ConstantInt::get(Int64Ty, 1);
    }
  }
  assert(Ret != nullptr &&
         "Failed to reconstruct array size for allocator: " + demangledName);
  Ret->setName(CI->getName() + ".array_size");
  return Ret;
} // GetArraySize

void HWAddressSanitizerPass::printPipeline(
    raw_ostream &OS, function_ref<StringRef(StringRef)> MapClassName2PassName) {
  static_cast<PassInfoMixin<HWAddressSanitizerPass> *>(this)->printPipeline(
      OS, MapClassName2PassName);
  OS << '<';
  if (Options.CompileKernel)
    OS << "kernel;";
  if (Options.Recover)
    OS << "recover";
  OS << '>';
}

/** Create constructor functions, and then hook them up appending their
 * reference to a global ctor list. Create globals metadata for runtime tagging.
 */
void HWAddressSanitizer::createHwasanCtorComdat() {
  std::tie(HwasanCtorFunction, std::ignore) =
      getOrCreateSanitizerCtorAndInitFunctions(
          M, kHwasanModuleCtorName, kHwasanInitName,
          /*InitArgTypes=*/{},
          /*InitArgs=*/{},
          // This callback is invoked when the functions are created the first
          // time. Hook them into the global ctors list in that case:
          [&](Function *Ctor, FunctionCallee) {
            Comdat *CtorComdat = M.getOrInsertComdat(kHwasanModuleCtorName);
            Ctor->setComdat(CtorComdat);
            appendToGlobalCtors(M, Ctor, 0, Ctor);
          });

  // Create a note that contains pointers to the list of global
  // descriptors. Adding a note to the output file will cause the linker to
  // create a PT_NOTE program header pointing to the note that we can use to
  // find the descriptor list starting from the program headers. A function
  // provided by the runtime initializes the shadow memory for the globals by
  // accessing the descriptor list via the note. The dynamic loader needs to
  // call this function whenever a library is loaded.
  //
  // The reason why we use a note for this instead of a more conventional
  // approach of having a global constructor pass a descriptor list pointer to
  // the runtime is because of an order of initialization problem. With
  // constructors we can encounter the following problematic scenario:
  //
  // 1) library A depends on library B and also interposes one of B's symbols
  // 2) B's constructors are called before A's (as required for correctness)
  // 3) during construction, B accesses one of its "own" globals (actually
  //    interposed by A) and triggers a HWASAN failure due to the initialization
  //    for A not having happened yet
  //
  // Even without interposition it is possible to run into similar situations in
  // cases where two libraries mutually depend on each other.
  //
  // We only need one note per binary, so put everything for the note in a
  // comdat. This needs to be a comdat with an .init_array section to prevent
  // newer versions of lld from discarding the note.
  //
  // Create the note even if we aren't instrumenting globals. This ensures that
  // binaries linked from object files with both instrumented and
  // non-instrumented globals will end up with a note, even if a comdat from an
  // object file with non-instrumented globals is selected. The note is harmless
  // if the runtime doesn't support it, since it will just be ignored.
  Comdat *NoteComdat = M.getOrInsertComdat(kHwasanModuleCtorName);
  // COMDAT -> way of representing something that should be included/discarded
  // as a unit

  Type *Int8Arr0Ty = ArrayType::get(Int8Ty, 0);
  auto *Start =
      new GlobalVariable(M, Int8Arr0Ty, true, GlobalVariable::ExternalLinkage,
                         nullptr, "__start_hwasan_globals");
  Start->setVisibility(GlobalValue::HiddenVisibility);
  auto *Stop =
      new GlobalVariable(M, Int8Arr0Ty, true, GlobalVariable::ExternalLinkage,
                         nullptr, "__stop_hwasan_globals");
  Stop->setVisibility(GlobalValue::HiddenVisibility);

  // Null-terminated so actually 8 bytes, which are required in order to align
  // the note properly.
  auto *Name = ConstantDataArray::get(*C, "LLVM\0\0\0");

  auto *NoteTy = StructType::get(Int32Ty, Int32Ty, Int32Ty, Name->getType(),
                                 Int32Ty, Int32Ty);
  auto *Note =
      new GlobalVariable(M, NoteTy, /*isConstant=*/true,
                         GlobalValue::PrivateLinkage, nullptr, kHwasanNoteName);
  Note->setSection(".note.hwasan.globals");
  Note->setComdat(NoteComdat);
  Note->setAlignment(Align(4));

  // The pointers in the note need to be relative so that the note ends up being
  // placed in rodata, which is the standard location for notes.
  auto CreateRelPtr = [&](Constant *Ptr) {
    return ConstantExpr::getTrunc(
        ConstantExpr::getSub(ConstantExpr::getPtrToInt(Ptr, Int64Ty),
                             ConstantExpr::getPtrToInt(Note, Int64Ty)),
        Int32Ty);
  };
  Note->setInitializer(ConstantStruct::getAnon(
      {ConstantInt::get(Int32Ty, 8),                           // n_namesz
       ConstantInt::get(Int32Ty, 8),                           // n_descsz
       ConstantInt::get(Int32Ty, ELF::NT_LLVM_HWASAN_GLOBALS), // n_type
       Name, CreateRelPtr(Start), CreateRelPtr(Stop)}));
  appendToCompilerUsed(M, Note);

  // Create a zero-length global in hwasan_globals so that the linker will
  // always create start and stop symbols.
  auto *Dummy = new GlobalVariable(
      M, Int8Arr0Ty, /*isConstantGlobal*/ true, GlobalVariable::PrivateLinkage,
      Constant::getNullValue(Int8Arr0Ty), "hwasan.dummy.global");
  Dummy->setSection("hwasan_globals");
  Dummy->setComdat(NoteComdat);
  Dummy->setMetadata(LLVMContext::MD_associated,
                     MDNode::get(*C, ValueAsMetadata::get(Note)));
  appendToCompilerUsed(M, Dummy);
}

/// Module-level initialization.
///
/// inserts a call to __hwasan_init to the module's constructor list.
void HWAddressSanitizer::initializeModule() {
  // LLVM_DEBUG(dbgs() << "Init " << M.getName() << "\n");
  TargetTriple = M.getTargetTriple();

  // HWASan may do short granule checks on function arguments read from the
  // argument memory (last byte of the granule), which invalidates writeonly.
  for (Function &F : M.functions())
    removeASanIncompatibleFnAttributes(F, /*ReadsArgMem=*/true);

  bool IsX86_64 = TargetTriple.getArch() == Triple::x86_64;

  InstrumentWithCalls = true;
  InstrumentStack = true;
  CompileKernel = false;
  if (ClFSAN_verbose) {
    errs() << "[FSAN] MEM ACCESS" << (ClFSAN_memAccesses ? " ON\n" : " OFF\n");
    errs() << "[FSAN] CHK INLINE"
           << (ClFSAN_memAccessesInline ? " ON\n" : " OFF\n");
    errs() << "[FSAN] MEM INTRIN" << (ClFSAN_memIntr ? " ON\n" : " OFF\n");
    errs() << "[FSAN] STACK" << (ClFSAN_stack ? " ON\n" : " OFF\n");
    errs() << "[FSAN] GLOBALS " << (ClFSAN_globals ? " ON\n" : " OFF\n");
    errs() << "[FSAN] BOP " << (ClFSAN_BOP ? " ON\n" : " OFF\n");
    errs() << "[FSAN] CMP " << (ClFSAN_CMP ? " ON\n" : " OFF\n");
    errs() << "[FSAN] GEP " << (ClFSAN_GEP ? " ON\n" : " OFF\n");
    errs() << "[FSAN] GLOBAL " << (ClFSAN_globals ? " ON\n" : " OFF\n");
    errs() << "[FSAN] HEAP " << (ClFSAN_heap ? " ON\n" : " OFF\n");
  }

  PointerTagShift = IsX86_64 ? 57 : 56;
  TBits = IsX86_64 ? 3 : 5;
  LBits = 2;

  LMask = ((1UL << LBits) - 1);
  TMask = ((1UL << TBits) - 1);
  RMask = ((1UL << (TBits + LBits)) - 1);

  LevelShift = IsX86_64 ? 3 : 5;
  TagMaskByte = IsX86_64 ? 0x3F : 0xFF;
  Mapping.init(TargetTriple, InstrumentWithCalls, CompileKernel);

  C = &(M.getContext());
  IRBuilder<> IRB(*C);
  InstrumentStack = ClFSAN_stack;
  HwasanCtorFunction = nullptr;
  createHwasanCtorComdat(); // creates the routine ctor with a call into the
                            // runtime function __hwasan_init

  if (ClFSAN_globals) {
    instrumentGlobals();
  }
  instrumentPersonalityFunctions();
  if (!TargetTriple.isAndroid()) {
    ThreadPtrGlobal = M.getOrInsertGlobal("__hwasan_tls", IntptrTy, [&] {
      auto *GV = new GlobalVariable(M, IntptrTy, /*isConstant=*/false,
                                    GlobalValue::ExternalLinkage, nullptr,
                                    "__hwasan_tls", nullptr,
                                    GlobalVariable::InitialExecTLSModel);
      appendToCompilerUsed(M, GV);
      return GV;
    });
  }
  FSANTaggingFunc = M.getOrInsertFunction("fsan_tag_memory", Int64Ty, PtrTy,
                                          PtrTy, Int64Ty, Int64Ty);
  // function for debugging inlined checks, some of them do not work
  // TODO: debug more
  __hwasan_loadN_explicit_function = M.getOrInsertFunction(
      "__hwasan_loadN_explicit", VoidTy, IntptrTy, Int8Ty, IntptrTy);
  assert(FSANTaggingFunc.getCallee() &&
         "FSAN tagging function must be declared");
}

void HWAddressSanitizer::initializeCallbacks(Module &M) {
  IRBuilder<> IRB(*C);
  const std::string MatchAllStr = UseMatchAllCallback ? "_match_all" : "";
  FunctionType *HwasanMemoryAccessCallbackSizedFnTy,
      *HwasanMemoryAccessCallbackFnTy, *HwasanMemTransferFnTy,
      *HwasanMemsetFnTy;
  if (UseMatchAllCallback) {
    HwasanMemoryAccessCallbackSizedFnTy =
        FunctionType::get(VoidTy, {IntptrTy, IntptrTy, Int8Ty}, false);
    HwasanMemoryAccessCallbackFnTy =
        FunctionType::get(VoidTy, {IntptrTy, Int8Ty}, false);
    HwasanMemTransferFnTy =
        FunctionType::get(PtrTy, {PtrTy, PtrTy, IntptrTy, Int8Ty}, false);
    HwasanMemsetFnTy =
        FunctionType::get(PtrTy, {PtrTy, Int32Ty, IntptrTy, Int8Ty}, false);
  } else {
    HwasanMemoryAccessCallbackSizedFnTy =
        FunctionType::get(VoidTy, {IntptrTy, IntptrTy}, false);
    HwasanMemoryAccessCallbackFnTy =
        FunctionType::get(VoidTy, {IntptrTy}, false);
    HwasanMemTransferFnTy =
        FunctionType::get(PtrTy, {PtrTy, PtrTy, IntptrTy}, false);
    HwasanMemsetFnTy =
        FunctionType::get(PtrTy, {PtrTy, Int32Ty, IntptrTy}, false);
  }

  for (size_t AccessIsWrite = 0; AccessIsWrite <= 1; AccessIsWrite++) {
    const std::string TypeStr = AccessIsWrite ? "store" : "load";
    const std::string EndingStr = ""; // Recover ? "_noabort" : "";

    HwasanMemoryAccessCallbackSized[AccessIsWrite] = M.getOrInsertFunction(
        ClMemoryAccessCallbackPrefix + TypeStr + "N" + MatchAllStr + EndingStr,
        HwasanMemoryAccessCallbackSizedFnTy);

    for (size_t AccessSizeIndex = 0; AccessSizeIndex < kNumberOfAccessSizes;
         AccessSizeIndex++) {
      HwasanMemoryAccessCallback[AccessIsWrite][AccessSizeIndex] =
          M.getOrInsertFunction(ClMemoryAccessCallbackPrefix + TypeStr +
                                    itostr(1ULL << AccessSizeIndex) +
                                    MatchAllStr + EndingStr,
                                HwasanMemoryAccessCallbackFnTy);
    }
  }

  const std::string MemIntrinCallbackPrefix =
      (CompileKernel && !ClKasanMemIntrinCallbackPrefix)
          ? std::string("")
          : ClMemoryAccessCallbackPrefix;

  HwasanMemmove = M.getOrInsertFunction(
      MemIntrinCallbackPrefix + "memmove" + MatchAllStr, HwasanMemTransferFnTy);
  HwasanMemcpy = M.getOrInsertFunction(
      MemIntrinCallbackPrefix + "memcpy" + MatchAllStr, HwasanMemTransferFnTy);
  HwasanMemset = M.getOrInsertFunction(
      MemIntrinCallbackPrefix + "memset" + MatchAllStr, HwasanMemsetFnTy);

  HwasanTagMemoryFunc = M.getOrInsertFunction(
      "__hwasan_tag_memory", VoidTy, PtrTy, Int8Ty, IntptrTy, IntptrTy);
  HwasanGenerateTagFunc =
      M.getOrInsertFunction("__hwasan_generate_tag", Int8Ty);

  HwasanRecordFrameRecordFunc =
      M.getOrInsertFunction("__hwasan_add_frame_record", VoidTy, Int64Ty);

  ShadowGlobal =
      M.getOrInsertGlobal("__hwasan_shadow", ArrayType::get(Int8Ty, 0));

  HwasanHandleVfork =
      M.getOrInsertFunction("__hwasan_handle_vfork", VoidTy, IntptrTy);
}

Value *HWAddressSanitizer::getOpaqueNoopCast(IRBuilder<> &IRB, Value *Val) {
  // An empty inline asm with input reg == output reg.
  // An opaque no-op cast, basically.
  // This prevents code bloat as a result of rematerializing trivial definitions
  // such as constants or global addresses at every load and store.
  InlineAsm *Asm =
      InlineAsm::get(FunctionType::get(PtrTy, {Val->getType()}, false),
                     StringRef(""), StringRef("=r,0"),
                     /*hasSideEffects=*/false);
  return IRB.CreateCall(Asm, {Val}, ".hwasan.shadow");
}

Value *HWAddressSanitizer::getDynamicShadowIfunc(IRBuilder<> &IRB) {
  return getOpaqueNoopCast(IRB, ShadowGlobal);
}

Value *HWAddressSanitizer::getShadowNonTls(IRBuilder<> &IRB) {
  if (Mapping.isFixed()) {
    return getOpaqueNoopCast(
        IRB, ConstantExpr::getIntToPtr(
                 ConstantInt::get(IntptrTy, Mapping.offset()), PtrTy));
  }

  if (Mapping.isInIfunc())
    return getDynamicShadowIfunc(IRB);

  Value *GlobalDynamicAddress =
      IRB.GetInsertBlock()->getParent()->getParent()->getOrInsertGlobal(
          kHwasanShadowMemoryDynamicAddress, PtrTy);
  return IRB.CreateLoad(PtrTy, GlobalDynamicAddress);
}

bool HWAddressSanitizer::ignoreAccessWithoutRemark(Instruction *Inst,
                                                   Value *Ptr) {
  // Do not instrument accesses from different address spaces; we cannot deal
  // with them.
  Type *PtrTy = cast<PointerType>(Ptr->getType()->getScalarType());
  if (PtrTy->getPointerAddressSpace() != 0)
    return true;

  // Ignore swifterror addresses.
  // swifterror memory addresses are mem2reg promoted by instruction
  // selection. As such they cannot have regular uses like an instrumentation
  // function and it makes no sense to track them as memory.
  if (Ptr->isSwiftError())
    return true;

  if (findAllocaForValue(Ptr)) {
    if (!InstrumentStack)
      return true;
    if (SSI && SSI->stackAccessIsSafe(*Inst))
      return true;
  }

  // if (isa<GlobalVariable>(getUnderlyingObject(Ptr))) {
  //   if (!InstrumentGlobals)
  //     return true;
  // TODO: Optimize inbound global accesses, like Asan `instrumentMop`.
  // }

  return false;
}

bool HWAddressSanitizer::ignoreAccess(OptimizationRemarkEmitter &ORE,
                                      Instruction *Inst, Value *Ptr) {
  bool Ignored = ignoreAccessWithoutRemark(Inst, Ptr);
  if (Ignored) {
    ORE.emit(
        [&]() { return OptimizationRemark(DEBUG_TYPE, "ignoreAccess", Inst); });
  } else {
    ORE.emit([&]() {
      return OptimizationRemarkMissed(DEBUG_TYPE, "ignoreAccess", Inst);
    });
  }
  return Ignored;
}

void HWAddressSanitizer::getInterestingMemoryOperands(
    OptimizationRemarkEmitter &ORE, Instruction *I,
    const TargetLibraryInfo &TLI,
    SmallVectorImpl<InterestingMemoryOperand> &Interesting) {
  // Skip memory accesses inserted by another instrumentation.
  // TODO : try and retrofit this
  if (I->hasMetadata(LLVMContext::MD_nosanitize))
    return;

  // Do not instrument the load fetching the dynamic shadow address.
  if (ShadowBase == I)
    return;

  if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
    // NOTE: this is masking undefined behavior from the runtime.
    // CFR: bug in 526.blender_r.
    // if (!ClInstrumentReads || ignoreAccess(ORE, I, LI->getPointerOperand()))
    //   return;
    Interesting.emplace_back(I, LI->getPointerOperandIndex(), false,
                             LI->getType(), LI->getAlign());
  } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
    // if (!ClInstrumentWrites || ignoreAccess(ORE, I, SI->getPointerOperand()))
    //   return;
    Interesting.emplace_back(I, SI->getPointerOperandIndex(), true,
                             SI->getValueOperand()->getType(), SI->getAlign());
  } else if (AtomicRMWInst *RMW = dyn_cast<AtomicRMWInst>(I)) {
    // if (!ClInstrumentAtomics || ignoreAccess(ORE, I,
    // RMW->getPointerOperand()))
    //   return;
    Interesting.emplace_back(I, RMW->getPointerOperandIndex(), true,
                             RMW->getValOperand()->getType(), std::nullopt);
  } else if (AtomicCmpXchgInst *XCHG = dyn_cast<AtomicCmpXchgInst>(I)) {
    // if (!ClInstrumentAtomics || ignoreAccess(ORE, I,
    // XCHG->getPointerOperand()))
    //   return;
    Interesting.emplace_back(I, XCHG->getPointerOperandIndex(), true,
                             XCHG->getCompareOperand()->getType(),
                             std::nullopt);
  } else if (auto *CI = dyn_cast<CallInst>(I)) {
    for (unsigned ArgNo = 0; ArgNo < CI->arg_size(); ArgNo++) {
      if (!ClInstrumentByval || !CI->isByValArgument(ArgNo))
        //||ignoreAccess(ORE, I, CI->getArgOperand(ArgNo))))
        continue;
      Type *Ty = CI->getParamByValType(ArgNo);
      Interesting.emplace_back(I, ArgNo, false, Ty, Align(1));
    }
    maybeMarkSanitizerLibraryCallNoBuiltin(CI, &TLI);
  }
}

static unsigned getPointerOperandIndex(Instruction *I) {
  if (LoadInst *LI = dyn_cast<LoadInst>(I))
    return LI->getPointerOperandIndex();
  if (StoreInst *SI = dyn_cast<StoreInst>(I))
    return SI->getPointerOperandIndex();
  if (AtomicRMWInst *RMW = dyn_cast<AtomicRMWInst>(I))
    return RMW->getPointerOperandIndex();
  if (AtomicCmpXchgInst *XCHG = dyn_cast<AtomicCmpXchgInst>(I))
    return XCHG->getPointerOperandIndex();
  report_fatal_error("Unexpected instruction");
  return -1;
}

static size_t TypeSizeToSizeIndex(uint32_t TypeSize) {
  size_t Res = llvm::countr_zero(TypeSize / 8);
  assert(Res < kNumberOfAccessSizes);
  return Res;
}

void HWAddressSanitizer::untagPointerOperand(Instruction *I, Value *Addr) {
  if (TargetTriple.isAArch64() || TargetTriple.getArch() == Triple::x86_64 ||
      TargetTriple.isRISCV64())
    return;

  IRBuilder<> IRB(I);
  Value *AddrLong = IRB.CreatePointerCast(Addr, IntptrTy);
  Value *UntaggedPtr =
      IRB.CreateIntToPtr(untagPointer(IRB, AddrLong), Addr->getType());
  I->setOperand(getPointerOperandIndex(I), UntaggedPtr);
}

Value *HWAddressSanitizer::memToShadow(Value *Mem, IRBuilder<> &IRB) {
  Value *XorVal =
      IRB.CreateXor(Mem, ConstantInt::get(IntptrTy, TRANS_CONSTANT));

#if defined(__x86_64__)
  // OFFSET only applies to x86 builds
  XorVal = IRB.CreateAdd(XorVal, ConstantInt::get(IntptrTy, OFFSET_MEM));
#endif

  return IRB.CreateIntToPtr(XorVal, PtrTy);
}

int64_t HWAddressSanitizer::getAccessInfo(bool IsWrite,
                                          unsigned AccessSizeIndex) {
  return /*(CompileKernel << HWASanAccessInfo::CompileKernelShift) |
         (MatchAllTag.has_value() << HWASanAccessInfo::HasMatchAllShift) |
         (MatchAllTag.value_or(0) << HWASanAccessInfo::MatchAllShift) |
         (Recover << HWASanAccessInfo::RecoverShift) |*/
      (IsWrite << HWASanAccessInfo::IsWriteShift) |
      (AccessSizeIndex << HWASanAccessInfo::AccessSizeShift);
}

// HWAddressSanitizer::ShadowTagCheckInfo
// HWAddressSanitizer::insertShadowTagCheck(Value *Ptr, Instruction
// *InsertBefore,
//                                          DomTreeUpdater &DTU, LoopInfo *LI)
//                                          {}

void HWAddressSanitizer::instrumentMemAccessOutline(Value *Ptr, bool IsWrite,
                                                    unsigned AccessSizeIndex,
                                                    Instruction *InsertBefore,
                                                    DomTreeUpdater &DTU,
                                                    LoopInfo *LI) {

  const int64_t AccessInfo = getAccessInfo(IsWrite, AccessSizeIndex);
  IRBuilder<> IRB(InsertBefore);
  bool UseFixedShadowIntrinsic = false;
  // The memaccess fixed shadow intrinsic is only supported on AArch64,
  // which allows a 16-bit immediate to be left-shifted by 32.
  // Since kShadowBaseAlignment == 32, and Linux by default will not
  // mmap above 48-bits, practically any valid shadow offset is
  // representable.
  // In particular, an offset of 4TB (1024 << 32) is representable, and
  // ought to be good enough for anybody.
  if (TargetTriple.isAArch64() && Mapping.isFixed()) {
    uint16_t OffsetShifted = Mapping.offset() >> 32;
    UseFixedShadowIntrinsic =
        static_cast<uint64_t>(OffsetShifted) << 32 == Mapping.offset();
  }

  if (UseFixedShadowIntrinsic) {
    IRB.CreateIntrinsic(Intrinsic::hwasan_check_memaccess_fixedshadow,
                        {Ptr, ConstantInt::get(Int32Ty, AccessInfo),
                         ConstantInt::get(Int64Ty, Mapping.offset())});
  } else {
    IRB.CreateIntrinsic(
        Intrinsic::hwasan_check_memaccess,
        {ShadowBase, Ptr, ConstantInt::get(Int32Ty, AccessInfo)});
  }
}

void HWAddressSanitizer::instrumentMemAccessInline(Value *Ptr, bool IsWrite,
                                                   unsigned AccessSizeIndex,
                                                   Instruction *InsertBefore,
                                                   DomTreeUpdater &DTU,
                                                   LoopInfo *LI) {
  ShadowTagCheckInfo R;
  // Accesses sizes are powers of two: 1, 2, 4, 8, 16.

  IRBuilder<> IRB(InsertBefore);
  R.PtrLong = IRB.CreatePointerCast(Ptr, IntptrTy);
  auto *Int128Ty = IntegerType::get(*C, 128);
  auto *Int16Ty = IntegerType::get(*C, 16);

  R.PtrTag = IRB.CreateTrunc(IRB.CreateLShr(R.PtrLong, PointerTagShift),
                             Int8Ty); // INT8

  Value *Shadow = memToShadow(R.PtrLong, IRB);
  R.MemTag = nullptr;
  Value *TagMismatch = nullptr;
  uint64_t ExtendPattern = 0ULL;
  LoadInst *LL;
  // extend ptr tag
  switch (AccessSizeIndex) {
  case 0:
    // errs() << "[FSAN] 1B access \n";
    // InsertBefore->dump();
    // errs() << "\n";
    LL = IRB.CreateLoad(R.PtrTag->getType(), Shadow);
    LL->setVolatile(true);
    R.MemTag = LL; // always fetch 64B
    TagMismatch = IRB.CreateICmpNE(R.PtrTag, R.MemTag);
    break;
  case 1:
    // errs() << "[FSAN] 2B access \n";
    // InsertBefore->dump();
    // errs() << "\n";
    R.PtrTag = IRB.CreateZExt(R.PtrTag, Int16Ty);
    ExtendPattern = 0x0101U; // pattern to extend the tag for 2-byte access
    R.PtrTag =
        IRB.CreateMul(R.PtrTag, ConstantInt::get(Int16Ty, ExtendPattern));
    LL = IRB.CreateLoad(R.PtrTag->getType(), Shadow); // always fetch 64B
    LL->setVolatile(true);
    R.MemTag = LL;
    TagMismatch = IRB.CreateICmpNE(R.PtrTag, R.MemTag);
    break;
  case 2:
    // errs() << "[FSAN] 4B access \n";
    // InsertBefore->dump();
    // errs() << "\n";
    R.PtrTag = IRB.CreateZExt(R.PtrTag, Int32Ty);
    ExtendPattern = 0x01010101UL; // pattern to extend the tag for 4-byte access
    R.PtrTag =
        IRB.CreateMul(R.PtrTag, ConstantInt::get(Int32Ty, ExtendPattern));
    LL = IRB.CreateLoad(R.PtrTag->getType(), Shadow); // always fetch 64B
    LL->setVolatile(true);
    R.MemTag = LL;
    TagMismatch =
        IRB.CreateICmpNE(R.PtrTag,
                         R.MemTag); // for 4-byte access, only the lowest 4
                                    // bytes of the memory tag are relevant
    break;
  case 3:
    // errs() << "[FSAN] 8B access \n";
    // InsertBefore->dump();
    // errs() << "\n";
    R.PtrTag = IRB.CreateZExt(R.PtrTag, Int64Ty);
    ExtendPattern =
        0x0101010101010101ULL; // pattern to extend the tag for 8-byte access
    R.PtrTag =
        IRB.CreateMul(R.PtrTag, ConstantInt::get(Int64Ty, ExtendPattern));
    LL = IRB.CreateLoad(R.PtrTag->getType(), Shadow); // always fetch 64B
    LL->setVolatile(true);
    R.MemTag = LL;
    TagMismatch =
        IRB.CreateICmpNE(R.PtrTag,
                         R.MemTag); // for 8-byte access, only the lowest 8
                                    // bytes of the memory tag are relevant
    break;
  case 4:
    // errs() << "[FSAN] 16B access \n";
    // InsertBefore->dump();
    // errs() << "\n";
    R.PtrTag = IRB.CreateZExt(R.PtrTag, Int128Ty);
    // Int128Ty already defined earlier:
    auto *Int128Ty = IntegerType::get(*C, 128);

    // Build a 128-bit APInt from a hex string (no "0x" prefix).
    APInt ExtendPattern(128, "01010101010101010101010101010101", 16);
    R.PtrTag =
        IRB.CreateMul(R.PtrTag, ConstantInt::get(Int128Ty, ExtendPattern));
    LL = IRB.CreateLoad(R.PtrTag->getType(), Shadow);
    LL->setVolatile(true);
    R.MemTag = LL;
    // APInt MaskPattern(128, "3F3F3F3F3F3F3F3F3F3F3F3F3F3F3F3F", 16);
    // R.MemTag = IRB.CreateAnd(R.MemTag, ConstantInt::get(Int128Ty,
    // MaskPattern));
    TagMismatch = IRB.CreateICmpNE(R.PtrTag, R.MemTag);
    break;
  }
  assert(R.MemTag && "MemTag should have been set in the switch statement");

  Value *MemoryIsTagged =
      IRB.CreateICmpNE(R.MemTag, ConstantInt::get(R.MemTag->getType(), 0x0UL));
  Value *PtrIsTagged =
      IRB.CreateICmpNE(R.PtrTag, ConstantInt::get(R.PtrTag->getType(), 0x0UL));

  Value *AllConditions = IRB.CreateAnd(PtrIsTagged, MemoryIsTagged);
  AllConditions = IRB.CreateAnd(AllConditions, TagMismatch);
  // AND: if (tag mismatch && memory is tagged && pointer is tagged)
  R.TagMismatchTerm = SplitBlockAndInsertIfThen(
      AllConditions, InsertBefore, false,
      MDBuilder(*C).createUnlikelyBranchWeights(), &DTU, LI);

  IRB.SetInsertPoint(R.TagMismatchTerm);

  InlineAsm *Asm;
  const int64_t AccessInfo = getAccessInfo(IsWrite, AccessSizeIndex);
  switch (TargetTriple.getArch()) {
  case Triple::x86_64:
    // The signal handler will find the data address in rdi.
    Asm = InlineAsm::get(
        FunctionType::get(VoidTy, {R.PtrLong->getType()}, false),
        "int3\nnopl " +
            itostr(0x40 + (AccessInfo & HWASanAccessInfo::RuntimeMask)) +
            "(%rax)",
        "{rdi}",
        /*hasSideEffects=*/true);
    break;
  case Triple::aarch64:
  case Triple::aarch64_be:
    // The signal handler will find the data address in x0.
    Asm = InlineAsm::get(
        FunctionType::get(VoidTy, {R.PtrLong->getType()}, false),
        "brk #" + itostr(0x900 + (AccessInfo & HWASanAccessInfo::RuntimeMask)),
        "{x0}",
        /*hasSideEffects=*/true);
    break;
  case Triple::riscv64:
    // The signal handler will find the data address in x10.
    Asm = InlineAsm::get(
        FunctionType::get(VoidTy, {R.PtrLong->getType()}, false),
        "ebreak\naddiw x0, x11, " +
            itostr(0x40 + (AccessInfo & HWASanAccessInfo::RuntimeMask)),
        "{x10}",
        /*hasSideEffects=*/true);
    break;
  default:
    report_fatal_error("unsupported architecture");
  }
  IRB.CreateCall(Asm, R.PtrLong); // TODO: bring back
}

void HWAddressSanitizer::instrumentMemIntrinsic(MemIntrinsic *MI) {
  auto arg0 = MI->getOperand(0);
  auto arg1 = MI->getOperand(1);
  if (!MI->getMetadata("fsan.instrument")) {
    // errs() << "[FSAN] NO FSAN MD INTRINSIC: " << *MI << "\n";
    // auto debugLoc = MI->getDebugLoc();
    // if (debugLoc)
    //   errs() << "\t[src loc] " << debugLoc->getFilename() << ":"
    //          << debugLoc->getLine() << "\n";
    return;
  }

  // NOTE: the above may introduce FNs
  // NO FPs observed on SPEC though

  IRBuilder<> IRB(MI);

  // TODO: memmove -> does not seem to be used in fuzzed software though
  // NOTE: memcmp is caught by the runtime interposition
  if (isa<MemTransferInst>(MI)) { /*memcpy, memmove*/
    SmallVector<Value *, 4> Args{
        arg0, arg1, IRB.CreateIntCast(MI->getOperand(2), IntptrTy, false)};

    if (UseMatchAllCallback)
      Args.emplace_back(ConstantInt::get(Int8Ty, *MatchAllTag));
    IRB.CreateCall(isa<MemMoveInst>(MI) ? HwasanMemmove : HwasanMemcpy, Args);
  } else if (isa<MemSetInst>(MI)) { /*memset*/
    SmallVector<Value *, 4> Args{
        MI->getOperand(0),
        IRB.CreateIntCast(MI->getOperand(1), IRB.getInt32Ty(), false),
        IRB.CreateIntCast(MI->getOperand(2), IntptrTy, false)};
    if (UseMatchAllCallback)
      Args.emplace_back(ConstantInt::get(Int8Ty, *MatchAllTag));
    IRB.CreateCall(HwasanMemset, Args);
  }
  MI->eraseFromParent();
  NumInstrumentedIntrinsics++;
} // instrumentMemIntrinsic

bool canBeSkipped(InterestingMemoryOperand &O, const DataLayout &DL) {
  // TODO: debug, might be removing too many checks
  if (AllocaInst *AI = dyn_cast<AllocaInst>(O.getPtr())) {
    if (AI->getAllocatedType()->isPointerTy() ||
        AI->getAllocatedType()->isIntegerTy() ||
        AI->getAllocatedType()->isFloatingPointTy()) {
      return true;
    }
  } // it's alloca
  // skip on globals with no "instrument" metadata
  if (GlobalVariable *GV = dyn_cast<GlobalVariable>(O.getPtr())) {
    if (!GV->getMetadata("fsan.instrument")) {
      return true;
    }
  }

  // if (GetElementPtrInst *I = dyn_cast<GetElementPtrInst>(O.getPtr())) {
  //   auto *MD_node = I->getMetadata("fsan.instrument");
  //   if (!MD_node) {
  //     // errs() << "[FSAN] Skipping instrumentation of GEP with no "
  //     //           "'instrument' metadata: "
  //     //        << *I << "\n";
  //     return true;
  //   }
  //   // else
  //   //   errs() << "[FSAN] Instrumenting ADDR with 'fsan.instrument'
  //   metadata: "
  //   //          << *I << "\n";
  // }
  // it could be a function argument, example: pTHX_ AV **const avp
  // we are not interested in accesses to ptr vars that are not in structs but
  // there is no way of telling them apart.per il

  // NOTE: DONT SKIP PTR LOADS!
  return false;
}

bool HWAddressSanitizer::instrumentMemAccess(InterestingMemoryOperand &O,
                                             DomTreeUpdater &DTU, LoopInfo *LI,
                                             const DataLayout &DL) {
  // TODO: remove checks on untagged ptrs
  // TODO: remove checks on non-struct types

  Value *Addr = O.getPtr();

  // If the pointer is statically known to be zero, the tag check will pass
  // since:
  // 1) it has a zero tag
  // 2) the shadow memory corresponding to address 0 is initialized to zero
  // and
  //    never updated.
  // We can therefore elide the tag check.
  llvm::KnownBits Known(DL.getPointerTypeSizeInBits(Addr->getType()));
  llvm::computeKnownBits(Addr, Known, DL);
  if (Known.isZero()) {
    return false;
  }

  if (O.MaybeMask)
    return false; // FIXME

  Instruction *I = O.getInsn();

  // might be UNSAFE?
  if (canBeSkipped(O, DL))
    return false;

  IRBuilder<> IRB(I);
  if (!O.TypeStoreSize.isScalable() && isPowerOf2_64(O.TypeStoreSize) &&
      (O.TypeStoreSize / 8 <= (1ULL << (kNumberOfAccessSizes - 1))) &&
      (!O.Alignment || *O.Alignment >= Mapping.getObjectAlignment() ||
       *O.Alignment >= O.TypeStoreSize / 8)) {
    size_t AccessSizeIndex = TypeSizeToSizeIndex(O.TypeStoreSize);

    if (!ClFSAN_memAccessesInline) {
      SmallVector<Value *, 2> Args{IRB.CreatePointerCast(Addr, IntptrTy)};
      IRB.CreateCall(HwasanMemoryAccessCallback[O.IsWrite][AccessSizeIndex],
                     Args);
    } else {
      instrumentMemAccessInline(Addr, O.IsWrite, AccessSizeIndex, I, DTU, LI);
      NumMemAccessesInlined++;
    }

  } else {
    SmallVector<Value *, 3> Args{
        IRB.CreatePointerCast(Addr, IntptrTy),
        IRB.CreateUDiv(IRB.CreateTypeSize(IntptrTy, O.TypeStoreSize),
                       ConstantInt::get(IntptrTy, 8))};
    IRB.CreateCall(HwasanMemoryAccessCallbackSized[O.IsWrite], Args);
    NumMemAccessesNotInlined++;
  }

  NumInstrumentedMemAccesses++;
  return true;
}

void HWAddressSanitizer::untagAlloca(IRBuilder<> &IRB, AllocaInst *AI,
                                     const DataLayout &DL) {
  /** Apply tag 0 to the previously tagged memory, immaterially of the type.
   */
  Value *NullTagVector = IRB.CreateIntToPtr(ConstantInt::get(IntptrTy, 0),
                                            PtrTy); // all zeroes tag vector
  IRB.CreateCall(
      FSANTaggingFunc,
      {IRB.CreatePointerCast(AI, PtrTy), NullTagVector,
       ConstantInt::get(Int64Ty, DL.getTypeAllocSize(AI->getAllocatedType())),
       ConstantInt::get(Int64Ty, 1)});

} // untagAlloca

void HWAddressSanitizer::tagAlloca(IRBuilder<> &IRB, AllocaInst *AI,
                                   const DataLayout &DL) {
  if (StructType *ST = dyn_cast<StructType>(AI->getAllocatedType())) {
    // force base depth = 0
    auto *TagVector = RetrieveOrCreateTagVector(ST, M, /*depth=*/0);
    assert(TagVector && "Tag vector must exist here - tagAlloca");
    IRB.CreateCall(FSANTaggingFunc,
                   {IRB.CreatePointerCast(AI, PtrTy),
                    IRB.CreatePointerCast(TagVector, PtrTy),
                    ConstantInt::get(Int64Ty, DL.getTypeAllocSize(ST)),
                    ConstantInt::get(Int64Ty, 1)});

  } // StructType
  else if (ArrayType *AT = dyn_cast<ArrayType>(AI->getAllocatedType())) {
    auto *InTY = AT->getElementType();
    int nElems = AT->getNumElements();
    int depth = 1;

    while (ArrayType *INAT = dyn_cast<ArrayType>(InTY)) {
      InTY = INAT->getElementType();
      nElems *= INAT->getNumElements();
      depth++;
    }
    auto *ST = dyn_cast<StructType>(InTY);
    assert(ST && "Innermost element type of array must be struct for RLT");
    auto *TV = RetrieveOrCreateTagVector(ST, M, depth);
    assert(TV && "Tag vector must exist here - tagAlloca");

    IRB.CreateCall(FSANTaggingFunc,
                   {IRB.CreatePointerCast(AI, PtrTy),
                    IRB.CreatePointerCast(TV, PtrTy),
                    ConstantInt::get(Int64Ty, DL.getTypeAllocSize(ST)),
                    ConstantInt::get(Int64Ty, nElems)});
  } // ArrayType

  else {
    errs() << "[FSAN] WARNING: Alloca of unsupported type for RLT: "
           << *(AI->getAllocatedType()) << "\n";
    errs() << "Is vector? " << AI->getAllocatedType()->isVectorTy() << "\n";
    errs() << "Is struct? " << AI->getAllocatedType()->isStructTy() << "\n";
    errs() << "Is array? " << AI->getAllocatedType()->isArrayTy() << "\n";
    errs() << "Is pointer? " << AI->getAllocatedType()->isPointerTy() << "\n";
    errs() << AI->getAllocatedType() << "\n";
  }
  return;
} // tagAlloca

unsigned HWAddressSanitizer::retagMask(unsigned AllocaNo) {
  if (TargetTriple.getArch() == Triple::x86_64)
    return AllocaNo & TagMaskByte;

  // A list of 8-bit numbers that have at most one run of non-zero bits.
  // x = x ^ (mask << 56) can be encoded as a single armv8 instruction for
  // these masks. The list does not include the value 255, which is used for
  // UAR.
  //
  // Because we are more likely to use earlier elements of this list than
  // later ones, it is sorted in increasing order of probability of collision
  // with a mask allocated (temporally) nearby. The program that generated
  // this list can be found at:
  // https://github.com/google/sanitizers/blob/master/hwaddress-sanitizer/sort_masks.py
  static const unsigned FastMasks[] = {
      0,   128, 64, 192, 32,  96,  224, 112, 240, 48, 16,  120,
      248, 56,  24, 8,   124, 252, 60,  28,  12,  4,  126, 254,
      62,  30,  14, 6,   2,   127, 63,  31,  15,  7,  3,   1};
  return FastMasks[AllocaNo % std::size(FastMasks)];
}

// Add a tag to an address.
Value *HWAddressSanitizer::tagPointer(IRBuilder<> &IRB, Type *Ty,
                                      Value *PtrLong, Value *Tag) {

  Value *TaggedPtrLong;
  Value *ShiftedTag = IRB.CreateShl(Tag, PointerTagShift);
  // ShiftedTag->setName("ShiftedTag");
  TaggedPtrLong = IRB.CreateOr(PtrLong, ShiftedTag);
  // TaggedPtrLong->setName("TaggedPtrLong");
  return IRB.CreateIntToPtr(TaggedPtrLong, Ty);
}

// Remove tag from an address.
inline Value *HWAddressSanitizer::untagPointer(IRBuilder<> &IRB,
                                               Value *PtrLong) {

  uint64_t mask = ~(TagMaskByte << PointerTagShift);
  Value *UntaggedPtrLong =
      IRB.CreateAnd(PtrLong, ConstantInt::get(PtrLong->getType(), mask));
  return UntaggedPtrLong;
}

inline Value *HWAddressSanitizer::untagPointerIntrinsic(IRBuilder<> &IRB,
                                                        Value *Ptr) {

  Type *PtrTy = Ptr->getType();
  unsigned PtrBits = M.getDataLayout().getPointerTypeSizeInBits(PtrTy);
  Type *MaskTy = IntegerType::get(M.getContext(), PtrBits);
  Value *MaskVal = ConstantInt::get(MaskTy, ~(TagMaskByte << PointerTagShift));
  // SIGNATURE: declare ptrty llvm.ptrmask(ptrty %ptr, intty %mask) speculatable
  // memory(none)
  Function *PtrMask =
      Intrinsic::getDeclaration(&M, Intrinsic::ptrmask, {PtrTy, MaskTy});
  Value *MaskedPtr = IRB.CreateCall(PtrMask, {Ptr, MaskVal});
  bool cond = MaskedPtr->getType() == Ptr->getType() &&
              (MaskedPtr->getType()->getPointerAddressSpace() ==
               Ptr->getType()->getPointerAddressSpace());
  assert(cond && "PTRMASK FUCKED UP");
  MaskedPtr->setName(Ptr->getName() + ".untagged");
  return MaskedPtr;
}

Value *HWAddressSanitizer::getHwasanThreadSlotPtr(IRBuilder<> &IRB) {
  // Android provides a fixed TLS slot for sanitizers. See TLS_SLOT_SANITIZER
  // in Bionic's libc/platform/bionic/tls_defines.h.
  constexpr int SanitizerSlot = 6;
  if (TargetTriple.isAArch64() && TargetTriple.isAndroid())
    return memtag::getAndroidSlotPtr(IRB, SanitizerSlot);
  return ThreadPtrGlobal;
}

Value *HWAddressSanitizer::getCachedFP(IRBuilder<> &IRB) {
  if (!CachedFP)
    CachedFP = memtag::getFP(IRB);
  return CachedFP;
}

Value *HWAddressSanitizer::getFrameRecordInfo(IRBuilder<> &IRB) {
  // Prepare ring buffer data.
  Value *PC = memtag::getPC(TargetTriple, IRB);
  Value *FP = getCachedFP(IRB);

  // Mix FP and PC.
  // Assumptions:
  // PC is 0x0000PPPPPPPPPPPP  (48 bits are meaningful, others are zero)
  // FP is 0xfffffffffffFFFF0  (4 lower bits are zero)
  // We only really need ~20 lower non-zero bits (FFFF), so we mix like this:
  //       0xFFFFPPPPPPPPPPPP
  //
  // FP works because in AArch64FrameLowering::getFrameIndexReference, we
  // prefer FP-relative offsets for functions compiled with HWASan.
  FP = IRB.CreateShl(FP, 44);
  return IRB.CreateOr(PC, FP);
}

bool HWAddressSanitizer::instrumentLandingPads(
    SmallVectorImpl<Instruction *> &LandingPadVec) {
  return true;
}

bool HWAddressSanitizer::instrumentStack(memtag::StackInfo &SInfo,
                                         const DominatorTree &DT,
                                         const PostDominatorTree &PDT,
                                         const LoopInfo &LI,
                                         const DataLayout &DL) {
  unsigned int I = 0;

  for (auto &KV : SInfo.AllocasToInstrument) {
    auto N = I++;
    auto *AI = KV.first;
    assert(AI && "Alloca must not be null");
    memtag::AllocaInfo &Info = KV.second;
    // assert(KV.second != nullptr && "AllocaInfo must not be null");
    Value *Tag = nullptr;
    int depth = 0;

    if (AllocaInst *AIcast = dyn_cast<AllocaInst>(AI)) {
      Type *allocatedType = AIcast->getAllocatedType();
      bool IsArray = allocatedType->isArrayTy();

      Type *TY = allocatedType;
      while (1) {
        if (ArrayType *AT = dyn_cast<ArrayType>(TY)) {
          TY = AT->getElementType();
          depth++;
        } else {
          break;
        }
      }

      if (depth == 0 && !TY->isStructTy()) {
        // not an array, not a struct -> SKIP
        continue;
      }

      if (IsArray && !TY->isStructTy()) {
        // multi-dim array of non-structs -> SKIP
        continue;
      }

      if (IsArray && TY->isStructTy()) {
        // multi-dim array of structs -> check if struct is safe
        StructType *ST = dyn_cast<StructType>(TY);
        if (ST->isLiteral()) {
          continue;
        }
        if (ST->getName().str().find("union.") == 0) {
          continue;
        }
        // TODO: can this improve performance?
        // if (ST->getName().str().empty()) {
        //   errs() << "[FSAN] UNNAMED ALLOCA SKIP " << *AI << "\n";
        //   continue;
        // }
      } else if (allocatedType->isStructTy()) {
        StructType *ST = dyn_cast<StructType>(allocatedType);
        if (ST->isLiteral()) {
          continue;
        }
        if (ST->getName().str().find("union.") == 0) {
          continue;
        }
        // TODO: can this improve performance?
        // if (ST->getName().str().empty()) {
        //   errs() << "[FSAN] ALLOCA SKIP " << *AI << "\n";
        //   continue;
        // }
      }
    } // cast AI
    else
      assert(false && "Allocas must be AllocaInsts");

    IRBuilder<> IRB(AI->getNextNonDebugInstruction());
    // NOTE: since root pointers are not tagged, no need for replacing the
    // pointer to the alloca with a tagged version.
    size_t Size = memtag::getAllocaSizeInBytes(*AI);
    Value *AICast = IRB.CreatePointerCast(AI, PtrTy);

    // TODO: in my case, this can go!
    auto HandleLifetime = [&](IntrinsicInst *II) {
      II->setArgOperand(0, ConstantInt::get(Int64Ty, Size));
      II->setArgOperand(1, AICast);
    };

    llvm::for_each(Info.LifetimeStart, HandleLifetime);
    llvm::for_each(Info.LifetimeEnd, HandleLifetime);

    // could be a struct or an array of structs. No unions, no literals

    if (ClFSAN_verbose) {
      errs() << "[FSAN-STACK] ALLOCA #" << N << "\n\t" << *AI << "\n\tSZ "
             << Size << " B\n\tFN " << demangle(AI->getFunction()->getName())
             << "\n";
      auto *Type = AI->getAllocatedType();
    }

    // ALL ALLOCAS PTRS are tagged when they're an aggregate
    auto *AILong = IRB.CreatePtrToInt(AI, IntptrTy);
    // LEVEL 0, T 0, R is set
    auto *TaggedAlloca = tagPointer(IRB, AI->getType(), AILong,
                                    ConstantInt::get(IntptrTy, RPTag));
    TaggedAlloca->setName(AI->getName() + ".tagged");

    AI->replaceUsesWithIf(TaggedAlloca, [AICast, AILong](const Use &U) {
      auto *User = U.getUser();
      return User != AILong && User != AICast && !isa<LifetimeIntrinsic>(User);
    });

    tagAlloca(IRB, AI, DL);

    auto TagEnd = [&](Instruction *Node) {
      IRB.SetInsertPoint(Node);
      untagAlloca(IRB, AI, DL);
      // NOTE: we still need to untag
    };

    for (auto *RI : SInfo.RetVec)
      TagEnd(RI);

    for (auto &II : Info.LifetimeStart)
      II->eraseFromParent();
    for (auto &II : Info.LifetimeEnd)
      II->eraseFromParent();
    // TODO: check if this is good or bad for performance
    // NOTE: I think it's legacy code + some stuff strictly necessary for NON
    // 1-to-1 shadow memory schemas
    memtag::alignAndPadAlloca(Info, Mapping.getObjectAlignment());

    memtag::annotateDebugRecords(Info, retagMask(N));

  } // for each alloca

  for (auto &I : SInfo.UnrecognizedLifetimes)
    I->eraseFromParent();
  return true;
} // instrumentStack

static void emitRemark(const Function &F, OptimizationRemarkEmitter &ORE,
                       bool Skip) {
  if (Skip) {
    ORE.emit([&]() {
      return OptimizationRemark(DEBUG_TYPE, "Skip", &F)
             << "Skipped: F=" << ore::NV("Function", &F);
    });
  } else {
    ORE.emit([&]() {
      return OptimizationRemarkMissed(DEBUG_TYPE, "Sanitize", &F)
             << "Sanitized: F=" << ore::NV("Function", &F);
    });
  }
}
bool isCallToBuiltinFunction(Instruction *Inst) {
  if (auto *CI = dyn_cast<CallBase>(Inst)) {
    if (Function *Callee = CI->getCalledFunction()) {
      return Callee->hasName() &&
             (Callee->getName().str().find("builtin") != std::string::npos);
    }
  }
  return false;
}

void HWAddressSanitizer::sanitizeFunction(Function &F,
                                          FunctionAnalysisManager &FAM) {
  if (&F == HwasanCtorFunction)
    return;

  // Do not apply any instrumentation for naked functions.
  if (F.hasFnAttribute(Attribute::Naked))
    return;

  if (!F.hasFnAttribute(Attribute::SanitizeHWAddress)) {
    return;
  }

  if (F.empty())
    return;
  // bool isCppConstructor = F.getName().str().find("C2E") != std::string::npos
  // ||
  //                         F.getName().str().find("C1E") != std::string::npos;

  NumTotalFuncs++;
  OptimizationRemarkEmitter &ORE =
      FAM.getResult<OptimizationRemarkEmitterAnalysis>(F);

  NumInstrumentedFuncs++;

  SmallVector<InterestingMemoryOperand, 16> OperandsToInstrument;
  SmallVector<MemIntrinsic *, 16> IntrinToInstrument;
  SmallVector<Instruction *, 8> LandingPadVec;
  SmallVector<GetElementPtrInst *, 40> GEPsToInstrument;
  SmallVector<CmpInst *, 40> CMPsToInstrument;
  SmallVector<CallBase *, 40> CallsToTypedAllocator;
  SmallVector<CallBase *, 40> CallsToTypedNew;
  SmallVector<StoreInst *, 40> StoresToInstrument;
  SmallVector<BinaryOperator *, 40> BOPsToInstrument;

  const TargetLibraryInfo &TLI = FAM.getResult<TargetLibraryAnalysis>(F);

  memtag::StackInfoBuilder SIB(SSI, DEBUG_TYPE);
  for (auto &Inst : instructions(F)) {

    if (InstrumentStack) {
      SIB.visit(ORE, Inst);
    }

    if (InstrumentLandingPads && isa<LandingPadInst>(Inst))
      LandingPadVec.push_back(&Inst);

    getInterestingMemoryOperands(ORE, &Inst, TLI, OperandsToInstrument);

    if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(&Inst))
      IntrinToInstrument.push_back(MI);

    if (GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(&Inst)) {
      GEPsToInstrument.push_back(GEPI);
    }

    if (CmpInst *CI = dyn_cast<CmpInst>(&Inst)) {
      CMPsToInstrument.push_back(CI);
    }

    // HEAP instrumentation: calls & invokes
    if (CallBase *CB = dyn_cast<CallBase>(&Inst)) {
      if (IsTypedAllocator(CB))
        CallsToTypedAllocator.push_back(CB);
      else {
        if (IsTypedNew(CB))
          CallsToTypedNew.push_back(CB);
      }
    }

    if (auto *BO = dyn_cast<BinaryOperator>(&Inst)) {
      if (BO->getOpcode() == Instruction::Sub) {
        // NOTE: only subs, because adding ptrs should be against the standard
        // NOTE: ptr subtractions make sense only if the two pointers point to
        // (parts of) the same object. Ow they are just undefined behavior.
        BOPsToInstrument.push_back(BO);
      }
      if (BO->getOpcode() == Instruction::Add) {
        // NOTE: only add, because adding ptrs should be against the standard
        // NOTE: ptr additions make sense only if one of the two operands is an
        // integer offset. Ow they are just undefined behavior.
        BOPsToInstrument.push_back(BO);
      }
    }
  }
  memtag::StackInfo &SInfo = SIB.get();

  initializeCallbacks(*F.getParent());

  if (!LandingPadVec.empty())
    instrumentLandingPads(LandingPadVec);

  if (SInfo.AllocasToInstrument.empty() && F.hasPersonalityFn() &&
      F.getPersonalityFn()->getName() == kHwasanPersonalityThunkName) {
    // __hwasan_personality_thunk is a no-op for functions without an
    // instrumented stack, so we can drop it.
    F.setPersonalityFn(nullptr);
  }

  if (SInfo.AllocasToInstrument.empty() && OperandsToInstrument.empty() &&
      IntrinToInstrument.empty() && GEPsToInstrument.empty() &&
      CMPsToInstrument.empty() && BOPsToInstrument.empty() &&
      CallsToTypedAllocator.empty() && CallsToTypedNew.empty())
    return;

  assert(!ShadowBase);

  BasicBlock::iterator InsertPt = F.getEntryBlock().begin();
  IRBuilder<> EntryIRB(&F.getEntryBlock(), InsertPt);
  /** NOTE: what is currently instrumented
   * 1) GLOBALS
   * 2) STACK
   * 3) GEPs
   * 4) HEAP
   * 5) CMP
   * 6) BOPs with PtrToInt operands
   * the type of the struct they point to)
   */

  if (ClFSAN_GEP) {
    for (auto &GEPI : GEPsToInstrument) {
      InstrumentGEP(GEPI);
    }
  } // TODO: can this be moved here?

  if (!SInfo.AllocasToInstrument.empty() && InstrumentStack) {
    const DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);
    const PostDominatorTree &PDT = FAM.getResult<PostDominatorTreeAnalysis>(F);
    const LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
    instrumentStack(SInfo, DT, PDT, LI, F.getDataLayout());
  }

  // If we split the entry block, move any allocas that were originally in the
  // entry block back into the entry block so that they aren't treated as
  // dynamic allocas.
  if (EntryIRB.GetInsertBlock() != &F.getEntryBlock()) {
    InsertPt = F.getEntryBlock().begin();
    for (Instruction &I :
         llvm::make_early_inc_range(*EntryIRB.GetInsertBlock())) {
      if (auto *AI = dyn_cast<AllocaInst>(&I))
        if (isa<ConstantInt>(AI->getArraySize()))
          I.moveBefore(F.getEntryBlock(), InsertPt);
    }
  }

  if (ClFSAN_heap) {
    for (auto *CB : CallsToTypedAllocator)
      RewriteMallocLikeCall(CB);
    for (auto *CB : CallsToTypedNew)
      RewriteNewCall(CB);
  }

  if (ClFSAN_memIntr && !IntrinToInstrument.empty()) {
    for (auto *Inst : IntrinToInstrument)
      instrumentMemIntrinsic(Inst);
  }

  if (ClFSAN_BOP) {
    for (auto &BOP : BOPsToInstrument) {
      InstrumentBOP(BOP);
    }
  }

  if (ClFSAN_CMP) {
    for (auto &CMPI : CMPsToInstrument) {
      InstrumentCMP(CMPI);
    }
  }

  if (ClFSAN_memAccesses) {
    DominatorTree *DT = FAM.getCachedResult<DominatorTreeAnalysis>(F);
    PostDominatorTree *PDT = FAM.getCachedResult<PostDominatorTreeAnalysis>(F);
    LoopInfo *LI = FAM.getCachedResult<LoopAnalysis>(F);
    DomTreeUpdater DTU(DT, PDT, DomTreeUpdater::UpdateStrategy::Lazy);
    const DataLayout &DL = F.getDataLayout();
    if (ClFSAN_memAccesses)
      for (auto &Operand : OperandsToInstrument)
        instrumentMemAccess(Operand, DTU, LI, DL);
    DTU.flush(); // TODO: does this have an interplay with optimizations?
  }

  ShadowBase = nullptr;
}

bool HWAddressSanitizer::IsTypedAllocator(CallBase *CB) {
  Value *V = CB->getCalledOperand()->stripPointerCasts();
  Function *Callee = dyn_cast<Function>(V);
  auto demangledName = Callee ? llvm::demangle(Callee->getName().str()) : "";
  return (Callee &&
          demangledName.find("typed_allocation") != std::string::npos);
}

bool HWAddressSanitizer::IsTypedNew(CallBase *CB) {
  Value *V = CB->getCalledOperand()->stripPointerCasts();
  Function *Callee = dyn_cast<Function>(V);
  auto demangledName = Callee ? llvm::demangle(Callee->getName().str()) : "";
  bool isOperatorNew = demangledName.find("operator new") != std::string::npos;
  bool AlignmentAware =
      demangledName.find("align_val_t") != std::string::npos && isOperatorNew;
  if (AlignmentAware) {
    // NOTE: these calls are rewritten in the frontend, hence they must be
    // handled here
    auto FullNameDemangled =
        Callee ? llvm::demangle(Callee->getName().str()) : "";
    errs() << "[FSAN] ALIGN-AWARE NEW " << FullNameDemangled
           << "\n\tCB:  " << *CB << "\n";
    if (CB->getDebugLoc()) {
      errs() << "\t at ";
      CB->getDebugLoc().print(errs());
      errs() << "\n";
    }
    // extract last param that is the typestring and print it
    errs() << "\t typestring: ";
    auto *LastParam = CB->getArgOperand(CB->arg_size() - 1);
    LastParam->print(errs());
    errs() << "\n";
    // NOTE: if n_args == 2, we skip this call
    if (CB->arg_size() == 2) {
      errs() << "\t [DBG] Skipping instrumentation of align-aware new with 2 "
                "args\n";
      return false;
    }
  }

  // return (Callee && demangledName.find("operator new") != std::string::npos
  // &&
  //         !AlignmentAware);
  return (Callee && demangledName.find("operator new") != std::string::npos);
}

void dumpGEPDebug(GetElementPtrInst *GEPI) {
  errs() << " _______________________________\n";
  errs() << " GEP INSTRUCTION: ";
  GEPI->print(errs());
  errs() << "\n";
  errs() << "\t SRC: ";
  errs() << *(GEPI->getOperand(0)) << "\n";
  errs() << *getUnderlyingObject(GEPI->getOperand(0)) << "\n";
  errs() << "\t SRC TYPE: ";
  GEPI->getSourceElementType()->print(errs());
  errs() << "\n";
  // if source type is struct, print if it's literal
  if (GEPI->getSourceElementType()->isStructTy()) {
    StructType *ST = dyn_cast<StructType>(GEPI->getSourceElementType());
    errs() << "\t\t Struct is literal: " << ST->isLiteral() << "\n";
  }
  errs() << "\t DST TYPE: ";
  auto res_type = GEPI->getResultElementType();
  res_type->print(errs());
  errs() << "\n";
  for (auto *User : GEPI->users()) {
    errs() << "\t\t GEP USER: ";
    User->print(errs());
    errs() << "\n";
  }
  errs() << " number of operands: " << GEPI->getNumOperands() << "\n";

  errs() << "\n _______________________________\n";
}

bool isCallToPtrmask(Value *V) {
  if (CallInst *CI = dyn_cast<CallInst>(V)) {
    auto *callee = CI->getCalledFunction();
    auto demangledName =
        callee && callee->hasName() ? demangle(callee->getName().str()) : "";
    return (callee && callee->hasName() &&
            callee->getName().str().find("llvm.ptrmask") != std::string::npos);
  }
  return false;
}

void HWAddressSanitizer::processOperand(Instruction *BOP, Value *OP, int idx) {
  if (PtrToIntInst *PTI = dyn_cast<PtrToIntInst>(OP)) {
    auto *PtrOp = PTI->getOperand(0);
    if (!isCallToPtrmask(PtrOp)) {
      IRBuilder<> IRB(BOP);
      auto *NewPtr = untagPointer(IRB, PTI);
      BOP->setOperand(idx, NewPtr);
    }
  }
}

PtrToIntInst *getBasePtrToInt(Value *V, int Depth = 0) {
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
      if (auto *Left = getBasePtrToInt(I->getOperand(0), Depth + 1))
        return Left;
      // Check right operand
      if (auto *Right = getBasePtrToInt(I->getOperand(1), Depth + 1))
        return Right;
      break;
    // You can add logic for PHI nodes or Trunc/ZExt if needed
    default:
      break;
    }
  }

  return nullptr;
}

bool checkIfPtr(Value *V) { return getBasePtrToInt(V) != nullptr; }

// detectin and handling arithmetics is still an open problem and very hard to
// tackle at IR
// TODO: this is overapproximated in that it does use help from FE and it does
// not keep into consideration the case in which both ops are pointers and then
// their result if used in the current BOP
void HWAddressSanitizer::InstrumentBOP(BinaryOperator *BOP) {
  auto DL = M.getDataLayout();
  auto *OP0 = BOP->getOperand(0);
  auto *OP1 = BOP->getOperand(1);
  IRBuilder<> IRB(BOP);

  if (BOP->getOpcode() == Instruction::Add) {
    /**
     * BOPsToInstrument
     * %282 = ptrtoint ptr %281 to i64, !dbg !866067
     * ...
     * %291 = load ptr, ptr %__pos_.i.fsan.scalar, align 8
     *  %292 = ptrtoint ptr %291 to i64,
        %293 = add i64 %282, -4, !dbg !866071
        %.neg = sub i64 0, %292, !dbg !866071
        %294 = add i64 %293, %.neg, !dbg !866071 <-
        %295 = lshr i64 %294, 2, !dbg !866071
        %296 = mul nuw i64 %295, 4, !dbg !866071
        %297 = add i64 %296, 4, !dbg !866071
        tail call void @llvm.memset.p0.i64(ptr align 4 %291, i8 -1, i64 %297,
     i1 false)
     */
    bool IsOp0Neg = OP0->hasName() &&
                    OP0->getName().str().find(".neg") != std::string::npos;
    bool IsOp1Neg = OP1->hasName() &&
                    OP1->getName().str().find(".neg") != std::string::npos;
    if (IsOp0Neg || IsOp1Neg) {
      assert(!(IsOp0Neg && IsOp1Neg) && "Both operands cannot be negations");
      Value *NegOp = IsOp0Neg ? OP0 : OP1;
      Value *OtherOp = IsOp0Neg ? OP1 : OP0;
      bool isOtherOpPtr = checkIfPtr(OtherOp);

      if (isOtherOpPtr) {
        PtrToIntInst *PTIOther = getBasePtrToInt(OtherOp);
        PtrToIntInst *PTINeg = getBasePtrToInt(NegOp);
        if (PTIOther && PTINeg) {

          auto *PtrOther = PTIOther->getOperand(0);
          auto *PtrNeg = PTINeg->getOperand(0);

          IRBuilder<> IRBOther(PTIOther);
          auto *NewPtrOther = untagPointerIntrinsic(IRBOther, PtrOther);
          PTIOther->setOperand(0, NewPtrOther);

          IRBuilder<> IRBNeg(PTINeg);
          auto *NewPtrNeg = untagPointerIntrinsic(IRBNeg, PtrNeg);
          PTINeg->setOperand(0, NewPtrNeg);
          return; // case ADD
        } else
          assert(false &&
                 "Both operands should have a ptrtoint in their def-use chain");
      }
    } // IsOp0Neg || IsOp1Neg
  } // if ADD

  // case SUB
  bool BothPtr = false;
  BothPtr = dyn_cast<PtrToIntInst>(OP0) && dyn_cast<PtrToIntInst>(OP1);

  bool IsPtr0 = dyn_cast<PtrToIntInst>(OP0) != nullptr;
  {
    // check if constexpr ptrtoint -> GLOBALS
    if (ConstantExpr *CE0 = dyn_cast<ConstantExpr>(OP0))
      if (CE0->getOpcode() == Instruction::PtrToInt)
        IsPtr0 = true;
    if (ConstantExpr *CE1 = dyn_cast<ConstantExpr>(OP1))
      if (CE1->getOpcode() == Instruction::PtrToInt)
        BothPtr = IsPtr0 && true;
  }

  if (!BothPtr) {
    // look for sub.ptr in the operands name
    if ((OP0->hasName() &&
         OP0->getName().str().find("sub.ptr") != std::string::npos &&
         OP0->getName().str().find(".cast") != std::string::npos) &&
        (OP1->hasName() &&
         OP1->getName().str().find("sub.ptr") != std::string::npos &&
         OP1->getName().str().find(".cast") != std::string::npos)) {
      BothPtr = true;
    }
  }

  if (!BothPtr) {
    FunctionCallee printf = M.getOrInsertFunction(
        "printf",
        FunctionType::get(IntegerType::getInt32Ty(M.getContext()),
                          PointerType::get(Type::getInt8Ty(M.getContext()), 0),
                          true));
    IRBuilder<> IRB(BOP);

    // errs() << "[FSAN] SKIP BOP " << *BOP << ", in function "
    //        << BOP->getFunction()->getName() << ", in file "
    //        << BOP->getFunction()->getParent()->getSourceFileName() << "\n";

    // NOTE: InstCombine + FrontEnd are responsible for this shame

    auto *PTI_LHS = getBasePtrToInt(OP0);
    auto *PTI_RHS = getBasePtrToInt(OP1);
    if (PTI_LHS && PTI_RHS && (BOP->getOpcode() == Instruction::Sub)) {
      // Value *FormatStr = IRB.CreateGlobalStringPtr(
      //     "BOP SKIP: %s, OP0: %s %p, OP1: %s %p, FUN %s\n");
      // bool isAdd = BOP->getOpcode() == Instruction::Add;
      // Value *FuncName = IRB.CreateGlobalStringPtr(isAdd ? "ADD" : "SUB");
      // Value *FUNC_NAME =
      //     IRB.CreateGlobalStringPtr(BOP->getFunction()->getName());
      // Value *OP0NAME_global = OP0->hasName()
      //                             ? IRB.CreateGlobalStringPtr(OP0->getName())
      //                             : IRB.CreateGlobalStringPtr("unnamed");
      // Value *OP1NAME_global = OP1->hasName()
      //                             ? IRB.CreateGlobalStringPtr(OP1->getName())
      //                             : IRB.CreateGlobalStringPtr("unnamed");
      // IRB.CreateCall(printf, {FormatStr, FuncName, OP0NAME_global, OP0,
      //                         OP1NAME_global, OP1, FUNC_NAME});
      errs() << "[FSAN] BOP CORNER CASE: " << *BOP << "\n";
      errs() << "\tOP0: " << *OP0 << "\n";
      errs() << "\tOP1: " << *OP1 << "\n";
      errs() << "\tPTI_LHS: " << *PTI_LHS << "\n";
      errs() << "\tPTI_RHS: " << *PTI_RHS << "\n";

      // TODO: does this introduce issues? With other related operations?
      IRBuilder IRB(PTI_LHS);
      auto *NewPtrLHS = untagPointerIntrinsic(IRB, PTI_LHS->getOperand(0));
      PTI_LHS->setOperand(0, NewPtrLHS);

      IRBuilder IRB2(PTI_RHS);
      auto *NewPtrRHS = untagPointerIntrinsic(IRB2, PTI_RHS->getOperand(0));
      PTI_RHS->setOperand(0, NewPtrRHS);
    } else {
      return;
      Value *FormatStr = IRB.CreateGlobalStringPtr(
          "BOP SKIP: %s, OP0: %s %p, OP1: %s %p, FUN %s\n");
      bool isAdd = BOP->getOpcode() == Instruction::Add;
      Value *FuncName = IRB.CreateGlobalStringPtr(isAdd ? "ADD" : "SUB");
      Value *FUNC_NAME =
          IRB.CreateGlobalStringPtr(BOP->getFunction()->getName());
      Value *OP0NAME_global = OP0->hasName()
                                  ? IRB.CreateGlobalStringPtr(OP0->getName())
                                  : IRB.CreateGlobalStringPtr("unnamed");
      Value *OP1NAME_global = OP1->hasName()
                                  ? IRB.CreateGlobalStringPtr(OP1->getName())
                                  : IRB.CreateGlobalStringPtr("unnamed");
      IRB.CreateCall(printf, {FormatStr, FuncName, OP0NAME_global, OP0,
                              OP1NAME_global, OP1, FUNC_NAME});
    }

    return;
  }

  // TODO: check if this is always true
  processOperand(BOP, OP0, 0); // OP0 is a ptrtoint
  processOperand(BOP, OP1, 1); // OP1 is a ptrtoint
}

bool isArrayOfAggregates(llvm::Type *T) {
  // Peel all array dimensions
  while (T->isArrayTy())
    T = T->getArrayElementType();

  // Check if the base element is an aggregate
  return T->isAggregateType();
}

// returns int value
Value *HWAddressSanitizer::extractLevelFromPointer(IRBuilder<> &IRB,
                                                   Value *Ptr) {
  // Extract the tag from the pointer using llvm.ptrmask with a mask that
  // isolates the LEVEL bits in the tag.
  Type *PtrTy = Ptr->getType();
  unsigned PtrBits = M.getDataLayout().getPointerTypeSizeInBits(PtrTy);
  Type *MaskTy = IntegerType::get(M.getContext(), PtrBits);
  uint64_t PtrMaskForLevel = LMask << (PointerTagShift + TBits);
  Value *MaskVal = ConstantInt::get(
      MaskTy, PtrMaskForLevel); // preserve L bits, not even R, still shifted
  Function *PtrMaskFcn =
      Intrinsic::getDeclaration(&M, Intrinsic::ptrmask, {PtrTy, MaskTy});

  Value *LevelShifted = IRB.CreateCall(PtrMaskFcn, {Ptr, MaskVal}); // AND
  Value *LevelShiftedInt = IRB.CreatePtrToInt(LevelShifted, IntptrTy);
  Value *Level =
      IRB.CreateLShr(LevelShiftedInt, PointerTagShift + TBits); // SHIFT
  Level->setName("FatherL");
  return Level;
}

Value *HWAddressSanitizer::zeroOutLevelBits(IRBuilder<> &IRB, Value *Ptr) {
  // ZERO level bits
  Type *PtrTy = Ptr->getType();
  unsigned PtrBits = M.getDataLayout().getPointerTypeSizeInBits(PtrTy);
  Type *MaskTy = IntegerType::get(M.getContext(), PtrBits);
  uint64_t PtrMaskForLevel = LMask << (PointerTagShift + TBits);
  Value *MaskVal = ConstantInt::get(MaskTy, ~PtrMaskForLevel);
  Function *PtrMaskFcn =
      Intrinsic::getDeclaration(&M, Intrinsic::ptrmask, {PtrTy, MaskTy});
  Value *PointerWithNoLevel = IRB.CreateCall(PtrMaskFcn, {Ptr, MaskVal});
  return PointerWithNoLevel;
}

Value *HWAddressSanitizer::maskPointerIntrinsic(IRBuilder<> &IRB, Value *Ptr,
                                                uint64_t MASK) {
  Type *PtrTy = Ptr->getType();
  unsigned PtrBits = M.getDataLayout().getPointerTypeSizeInBits(PtrTy);
  Type *MaskTy = IntegerType::get(M.getContext(), PtrBits);
  Value *MaskVal = ConstantInt::get(MaskTy, MASK);
  Function *PtrMaskFcn =
      Intrinsic::getDeclaration(&M, Intrinsic::ptrmask, {PtrTy, MaskTy});
  Value *MaskedPtr = IRB.CreateCall(PtrMaskFcn, {Ptr, MaskVal});
  return MaskedPtr;
}

Value *HWAddressSanitizer::AddOneModuloSomething(IRBuilder<> &IRB,
                                                 Value *Addendum,
                                                 uint64_t Mask) {
  Value *PlusOne =
      IRB.CreateAdd(Addendum, ConstantInt::get(Addendum->getType(), 1));
  PlusOne = IRB.CreateAnd(PlusOne, ConstantInt::get(PlusOne->getType(),
                                                    LMask)); // % LEVEL MAX
  return PlusOne;
}

// TODO: introduce two instrumentGEP, one to tag with T bits only scalar
// pointers, the other one to tag with R, L and T bits depending on compile-time
// settings
void HWAddressSanitizer::InstrumentGEP(GetElementPtrInst *GEPI) {
  auto nOperands = GEPI->getNumOperands();
  Value *sonTag = nullptr;
  Value *sonIdx = nullptr;

  bool guard = false;
  assert(nOperands <= 3);
  auto SrcType = GEPI->getSourceElementType();
  auto DstType = GEPI->getResultElementType();
  auto PtrOp = GEPI->getPointerOperand();
  auto GEPNAME = GEPI->hasName() ? GEPI->getName().str()
                                 : "gep." + itostr(NumInstrumentedGEPs);
  auto PTR_OP_NAME = GEPI->getPointerOperand()->hasName()
                         ? GEPI->getPointerOperand()->getName().str()
                         : "gep.ptr.op." + itostr(NumInstrumentedGEPs);

  if (GEPI->getType()->isVectorTy()) {
    // NOTE: if loops are being vectorized, this will happen. TODO.
    assert(false && "This should not happen if loop opts are disabled");
  }

  IRBuilder<> IRB(GEPI->getNextNonDebugInstruction());

  std::string endResultName = "";
  Value *taggedPointer = nullptr;
  bool isScalar = false;
  uint64_t PTR_MASK = ((1ULL << PointerTagShift) - 1);
  uint64_t L_MASK = ((LMask << (PointerTagShift + TBits)));
  uint64_t R_MASK = (1ULL << (PointerTagShift + TBits + LBits));
  uint64_t RGTFO =
      L_MASK | PTR_MASK; // preserve L, remove R for safety, T is unused

  Value *FatherLevel = nullptr; // level of ptr operand, only computed if needed
  if (SrcType->isArrayTy()) {
    // if N-dimensional array of structs, L=L+1, R set, T unused (WIP)
    // if array of non-structs, L=L, R=0, T=idx
    bool isAggregateOfStructs = isArrayOfAggregates(DstType);
    bool DstIsStruct = DstType->isStructTy();

    if (DstIsStruct || (isAggregateOfStructs)) {
      // L=L+1 if struct, L if decay/add
      // R always set
      // T unused
      Value *untaggedResult = zeroOutLevelBits(
          IRB, GEPI); // R is still SET, L is zeroed out, T is unused
      Value *Tag = nullptr;

      bool isDecayAdd =
          GEPI->getName().str().find("add.ptr") != std::string::npos;
      bool IsArrayIdx = GEPI->hasName() && GEPI->getName().str().find(
                                               "arrayidx") != std::string::npos;
      if (isDecayAdd || IsArrayIdx) {
        if (ClFSAN_verbose) {
          errs() << "ARRAY DECAY + STRUCT GEP: ";
          GEPI->print(errs());
          errs() << "\n";
        }
        taggedPointer = GEPI;
        endResultName =
            GEPNAME + ".fsan" + (DstIsStruct ? ".struct" : ".array");
      } else {

        Value *RUnset = maskPointerIntrinsic(
            IRB, untaggedResult, RGTFO); // remove R, preserve L, T is unused
        Value *RUnsetLong = IRB.CreatePtrToInt(RUnset, IntptrTy);
        Value *Increment =
            ConstantInt::get(IntptrTy, (1ULL << (TBits + PointerTagShift)));
        Value *PtrLongIncremented =
            IRB.CreateAdd(RUnsetLong, Increment); // L = L + 1

        uint64_t R_MASK = (1ULL << (PointerTagShift + TBits + LBits));
        Value *PtrLongIncWithRSet = IRB.CreateOr(
            PtrLongIncremented, ConstantInt::get(IntptrTy, R_MASK)); // set R
        taggedPointer = IRB.CreateIntToPtr(PtrLongIncWithRSet, GEPI->getType());
      }

    } // GEP array->aggregate
    else {
      // array of non-structs. Preserve L, we are flattening it.
      // L = L, R = 0, T = idx
      taggedPointer = GEPI;
      endResultName = GEPNAME + ".fsan.scalar.array";
    }
  } // GEP from array type

  else { /** father is not array */
    if (SrcType->isStructTy()) {
      StructType *ST = dyn_cast<StructType>(SrcType);
      bool tag = true;
      // NOTE: unnamed structs are used in extractvalues and might be a sign of
      // type coercion

      if (ST && !ST->hasName() && ClSkipUnnamedStructs) {
        // IDEA: remove FPs caused by type coercion happening
        // 1. when passing structs by value
        // 2. when using extractvalue on structs passed by value
        // 3. when a function returns a struct by value and it's immediately
        // (cfr std::make_tuple) used in a GEP
        // TODO: what else is there?
        // TODO: handle case by case to avoid FNs

        StructType *GEPST = dyn_cast<StructType>(GEPI->getSourceElementType());
        Value *GEPPtrOp = GEPI->getPointerOperand();
        if (AllocaInst *AI = dyn_cast<AllocaInst>(GEPPtrOp)) {
          Type *AIType = AI->getAllocatedType();
          if (AIType->isStructTy()) {
            StructType *AllocaST = dyn_cast<StructType>(AIType);
            // compare two structs layouts
            auto nFieldsAIST = AllocaST->getNumElements();
            auto nFieldsGEPST = GEPST->getNumElements();

            // NOTE: this fixes issues when returning/passing a struct by value
            // (cfr 403.gcc, 462.libquantum, 525.x264_r)
            if (nFieldsAIST != nFieldsGEPST) {
              // H1: very coarse
              errs() << "[FSAN] Presumably compiler-induced type punning "
                        "detected\n\t\tAlloca struct type: "
                     << *AllocaST << "\n\t\tGEP struct type: " << *GEPST
                     << "\n\t\tGEP instruction: " << *GEPI << "\n";
              tag = false;
              auto DebugLoc = GEPI->getDebugLoc();
              if (DebugLoc) {
                errs() << "\t\t at ";
                DebugLoc.print(errs());
                errs() << "\n";
              }
            } // H1 -> different N of fields

            /**
             * %"struct.std::__1::pair.21" = type { %struct.anon,
             * %struct.anon }
             * could be cast to
             * {ptr, ptr} if struct.anon = {ptr}
             */
            else {
              // NOTE: this fixes weird cases in which structs with just one
              // field are nested into each other (cfr iterator pair in
              // 541.leela_r)
              bool layoutsMatch = true;
              for (unsigned i = 0; i < nFieldsAIST; i++) {
                Type *FieldTypeAIST = AllocaST->getElementType(i);
                Type *FieldTypeGEPST = GEPST->getElementType(i);
                if (FieldTypeAIST != FieldTypeGEPST) {
                  layoutsMatch = false;
                  break;
                }
              }
              if (!layoutsMatch) {
                // H2: more precise, still overapproximation but less than H1
                errs() << "[FSAN] Presumably compiler-induced type punning "
                          "detected based on struct layout "
                          "mismatch\n\t\tAlloca struct type: "
                       << *AllocaST << "\n\t\tGEP struct type: " << *GEPST
                       << "\n\t\tGEP instruction: " << *GEPI << "\n";
                tag = false;
                auto DebugLoc = GEPI->getDebugLoc();
                if (DebugLoc) {
                  errs() << "\t\t at ";
                  DebugLoc.print(errs());
                  errs() << "\n";
                }
              }
              // TODO: can this open up to FNs?
            }
          } // AI->isStruct

        } // if ALLOCA
        else {

          errs() << "[FSAN] GEP pointer operand is not an alloca: " << *GEPPtrOp
                 << "\n\tunderlying object: " << *getUnderlyingObject(GEPPtrOp)
                 << "\n\t GEP: " << *GEPI << "\n";

          if (GEPPtrOp->hasName() &&
              GEPPtrOp->getName().find("coerce.") != std::string::npos) {
            errs() << "[FSAN] HEURISTIC - GEP with coerce in name: " << *GEPI
                   << "\n";
            tag = false;
          } // HEUR 2
          tag = false; // BE CONSERVATIVE IN CASE OF ANON STRUCT GEP

          // TODO: since some ptrs might tagged already, try and "revert" the
          // tagging logic to revel the original pointer
          // if PTR comes from LOAD -> conservatively untag GEP

          // if PTR is alloca (pot. fsan-tagged), get base alloca and do checks
          // on type

          // if it's heap-alloc, try and get the type from call to fsan
          // tagging function?

          // if it's array idx, try and get type from GEP (it's a GEP)
        }

        // H: is pointers to a certain struct are used in extractvalue, type
        // coercion
      }

      // if (ST && ST->hasName() && ST->getName().str().find("union.") == 0) {
      //   tag = false;
      //   GEPI->setMetadata("fsan_skip_gep", MDNode::get(M.getContext(), {}));
      // }

      // if (ST && ST->hasName()) {
      //   auto demangledName = demangle(ST->getName().str());
      //   for (auto &pattern : FilterSet) {
      //     // TODO: finish this
      //     if (demangledName.find(pattern) != std::string::npos) {
      //       errs() << "[FSAN] GEP BLOCK: " << pattern << ", GEP: ";
      //       GEPI->print(errs());
      //       errs() << "\n";
      //       tag = false;
      //       break;
      //     }
      //   }
      // }

      // GEPs on anon structs might be a symptom of type coercion, which is a
      // common source of FPs
      // if (ST && ST->hasName()) {
      //   auto demangledName = demangle(ST->getName().str());
      //   if ((demangledName.find("class.anon") != std::string::npos) ||
      //       (demangledName.find("struct.anon") != std::string::npos)) {
      //     errs() << "[FSAN] GEP BLOCK: anon struct, GEP: ";
      //     GEPI->print(errs());
      //     errs() << "\n";
      //     tag = false;
      //   }
      // }
      // TODO: introduce tunables for the above cases

      sonTag = nullptr;
      auto sonIsScalar = !DstType->isStructTy() && !DstType->isVectorTy();
      bool sonIsArrayOfAggregates = isArrayOfAggregates(DstType);

      if (sonIsScalar && !sonIsArrayOfAggregates && tag) {
        uint64_t idx = -1;
        auto op2 = GEPI->getOperand(2);
        uint64_t T = -1;
        if (ConstantInt *CI = dyn_cast<ConstantInt>(op2)) {
          idx = (uint64_t)CI->getZExtValue();
          uint64_t IdxModuloT_MAX = (idx + 1) % T_MAX;
          uint64_t IdxDivT_MAX = (idx + 1) / T_MAX;
          T = (IdxModuloT_MAX + IdxDivT_MAX);
          T = T % T_MAX;
          if (T == 0)
            T = 1;
          sonTag = ConstantInt::get(IntptrTy, T);
        } else
          assert(false && "Non-constant GEP index?");

        // unset R, preserve L and set T
        uint64_t PTR_MASK = ((1ULL << PointerTagShift) - 1);
        uint64_t L_MASK = ((LMask << TBits)) << (PointerTagShift);
        uint64_t MASK = PTR_MASK | L_MASK; // zero out R and T, preserve L
        Value *untagged = maskPointerIntrinsic(IRB, GEPI, MASK);
        Value *untaggedLong = IRB.CreatePtrToInt(untagged, IntptrTy);
        Value *TBits_CONST = ConstantInt::get(IntptrTy, T << (PointerTagShift));
        Value *untaggedLongWithT =
            IRB.CreateOr(untaggedLong, TBits_CONST); // SET T
        taggedPointer = IRB.CreateIntToPtr(untaggedLongWithT, GEPI->getType());

        endResultName = GEPNAME + ".fsan.scalar";
        isScalar = true;
      } // GEP struct -> scalar
      else if (!tag) {
        // sometimes, we might not want to tag the GEP
        taggedPointer = untagPointerIntrinsic(IRB, GEPI);
        endResultName = GEPNAME + ".fsan.untagged";
      } else {
        // tag = 1
        // result is either aggregate or array of aggregates -> L=L+1, R set, T
        // unused
        if (DstType->isAggregateType()) {
          /** GEP: struct -> aggregate */
          // L = L + 1 if not decay, L = L if decay (since we are still indexing
          // the first level of the struct), R = 1, T = unused set R Value
          // *untaggedResult = untagPointerIntrinsic(IRB, GEPI);

          bool isDecayAdd =
              GEPI->getName().str().find("add.ptr") != std::string::npos;
          bool IsArrayIdx =
              GEPI->hasName() &&
              GEPI->getName().str().find("arrayidx") != std::string::npos;
          if (isDecayAdd || IsArrayIdx) {
            if (ClFSAN_verbose) {
              errs() << "ARRAY DECAY + STRUCT GEP: ";
              GEPI->print(errs());
              errs() << "\n";
            }

            taggedPointer = GEPI;
            endResultName = GEPNAME + ".fsan" +
                            (DstType->isStructTy() ? ".struct" : ".array");
          }

          else {
            // TODO: optimize this case! Some benchmark might not compile due to
            // excessive register pressure
            Value *RUnset = maskPointerIntrinsic(IRB, GEPI, RGTFO);
            // UNSET R to prevent bad math
            Value *RUnsetLong = IRB.CreatePtrToInt(RUnset, IntptrTy);
            Value *Increment =
                ConstantInt::get(IntptrTy, (1ULL << (TBits + PointerTagShift)));
            Value *PtrLongIncremented = IRB.CreateAdd(RUnsetLong, Increment);
            Value *PtrLongIncWithRSet =
                IRB.CreateOr(PtrLongIncremented,
                             ConstantInt::get(IntptrTy, R_MASK)); // set R
            taggedPointer =
                IRB.CreateIntToPtr(PtrLongIncWithRSet, GEPI->getType());
            endResultName = GEPNAME + ".fsan" +
                            (DstType->isStructTy() ? ".struct" : ".array");
          }
        }
      } // else - son is either not scalar or arrayOfAggregates
    } // FATHER IS STRUCT
    else {
      // SRC Type is neither an array nor a struct -> what is it then?
      if (ClFSAN_verbose) {
        errs() << "[FSAN] OTHER GEP " << "\n\tGEP: ";
        GEPI->print(errs());
        errs() << "\n\tSRC: ";
        errs() << *(GEPI->getOperand(0)) << "\n";
        errs() << "\n\tSRC TYPE: ";
        GEPI->getSourceElementType()->print(errs());
        errs() << "\n\tDST TYPE: ";
        GEPI->getResultElementType()->print(errs());
        errs() << "\n";
        // EXAMPLE getelementptr inbounds i8, ptr %ins.tagged, i64 %vbase.offset
        auto IdxOperand = GEPI->getOperand(1);
        auto NameIdxOperand =
            IdxOperand->hasName() ? IdxOperand->getName().str() : "";
        if (NameIdxOperand.find("vbase.offset") != std::string::npos) {
          errs() << "\t\tGEP ON BASE OF VIRTUAL INHERITANCE\n";
          errs() << "NAME OF IDX OPERAND: " << NameIdxOperand << "\n";
          // TODO: how do I figure out nesting level??
        }
      }

      return;
    }
  } // else - father is not an array

  if (!taggedPointer) {
    // errs() << "[FSAN] WARNING: tagged pointer unset ";
    // GEPI->print(errs());
    // errs() << "\n";
    return; // TODO: handle corner cases
  }
  assert(taggedPointer->isPointerTy() &&
         "Tagged pointer must be of pointer type");
  llvm::Type *ptrTy = taggedPointer->getType();
  taggedPointer->setName(endResultName);

  GEPI->replaceUsesWithIf(
      taggedPointer, [GEPI, isScalar, DstType](const Use &U) {
        auto *User = U.getUser();

        // do not replace in these calls, they are used to remove tag
        if (CallBase *CB = dyn_cast<CallBase>(User)) {
          if (CB->getCalledFunction() && CB->getCalledFunction()->hasName() &&
              CB->getCalledFunction()->getName().find("llvm.ptrmask") !=
                  std::string::npos) {
            return false; // no repl
          }
        } // call to mask ptr

        if (isa<LifetimeIntrinsic>(User)) {
          return false; // no repl
        }

        bool safe = true;

        // NOTE: do not tag pointers used to access vtable
        if (StoreInst *SI = dyn_cast<StoreInst>(User)) {
          if (SI->getPointerOperand() == GEPI) {
            Value *storedVal = SI->getValueOperand();
            // Try match a CONST EXPR GEP to some global var named "vtable
            // for"
            /** EXAMPLE:
             *  STORE USER:
             * store ptr getelementptr inbounds inrange(-16, 112) ({ [16 x ptr]
             }, ptr @_ZTVSt15basic_streambufIcSt11char_traitsIcEE, i32 0, i32 0,
             i32 2), ptr %111, align 8, !dbg !6833, !tbaa !5818, !DIAssignID
             !6834
            */
            if (GEPOperator *CE = dyn_cast<GEPOperator>(storedVal)) {
              if (CE->isInBounds() && CE->getNumOperands() >= 3) {
                // OP0 is an external unnamed constant array of ptrs
                // EXAMPLE ->  GEP OPERAND 0:
                // @_ZTVNSt7__cxx1115basic_stringbufIcSt11char_traitsIcESaIcEEE
                // = external unnamed_addr constant { [16 x ptr] }, align 8
                if (GlobalVariable *GV =
                        dyn_cast<GlobalVariable>(CE->getOperand(0))) {
                  if (GV->hasName() &&
                      demangle(GV->getName().str()).find("vtable for") == 0) {
                    safe = false;
                  }
                }
              }
            } // if GEPOperator
          }
        } // store in VTable

        if (!safe) {
          if (ClFSAN_verbose) {
            errs() << "[FSAN] NOT REPLACING USE IN USER: ";
            User->print(errs());
            errs() << "\n";
          }
        }
        return safe;
      });
  NumInstrumentedGEPs++;
} // InstrumentGEP

void HWAddressSanitizer::InstrumentCMP(CmpInst *CI) {
  /** Instrumenting CMPs with no filters */
  auto op1 = CI->getOperand(0);
  auto cmpType = op1->getType();
  auto op2 = CI->getOperand(1);
  if (cmpType->isPointerTy()) {
    IRBuilder<> IRB(CI);
    Value *untaggedPtr1 = untagPointerIntrinsic(IRB, op1);
    CI->replaceUsesOfWith(op1, untaggedPtr1);
    Value *untaggedPtr2 = untagPointerIntrinsic(IRB, op2);
    CI->replaceUsesOfWith(op2, untaggedPtr2);
    NumInstrumentedCMPs++;
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
      NumInstrumentedCMPs++;
    } else {
      return;
      IRBuilder<> IRB(CI);
      FunctionCallee printf = M.getOrInsertFunction(
          "printf",
          FunctionType::get(
              IntegerType::getInt32Ty(M.getContext()),
              PointerType::get(Type::getInt8Ty(M.getContext()), 0), true));
      Value *FormatStr =
          IRB.CreateGlobalStringPtr("CMP SKIP: %s, OP0: %s %p, OP1: %s %p\n");
      Value *FUNC_NAME =
          IRB.CreateGlobalStringPtr(CI->getFunction()->getName());
      Value *OP0NAME_global = op1->hasName()
                                  ? IRB.CreateGlobalStringPtr(op1->getName())
                                  : IRB.CreateGlobalStringPtr("unnamed");
      Value *OP1NAME_global = op2->hasName()
                                  ? IRB.CreateGlobalStringPtr(op2->getName())
                                  : IRB.CreateGlobalStringPtr("unnamed");
      IRB.CreateCall(printf, {FormatStr, FUNC_NAME, OP0NAME_global, op1,
                              OP1NAME_global, op2});
    }
  }
} // InstrumentCMP

StructType *HWAddressSanitizer::getStructTypeFromDbgInfo(GlobalVariable *GV,
                                                         int *numElements,
                                                         bool *isUnion) {
  auto *MDNode = GV->getMetadata("dbg");
  int depth = 0;
  if (!MDNode) {
    return nullptr;
  }
  // errs() << "[FSAN] DBG INFO FOR GV " << GV->getName() << "\n";
  DIGlobalVariableExpression *DIE =
      dyn_cast<DIGlobalVariableExpression>(MDNode);

  auto *di_type = DIE->getVariable()->getType();
  DICompositeType *arrayType = dyn_cast<DICompositeType>(di_type),
                  *cur = nullptr;

  // TODO: also N of elements
  while (arrayType && arrayType->getTag() == dwarf::DW_TAG_array_type) {
    // arrayType->dump();
    depth++;
    cur = arrayType; // this will be set to the last type that is not array
    arrayType = dyn_cast<DICompositeType>(arrayType->getBaseType());
  }
  // if arrayType is null, we reached a DerivedType or a StructType
  // if arrayType is still set, it's an array of some other composite type?

  // errs() << "EOF parsing of DBG INFO for GV " << GV->getName() << "\n";
  // if (cur) {
  //   errs() << "DIC: \n";
  //   // cur->dump();
  //   // cur->getBaseType()->dump();
  // }

  std::string structName = "";
  StructType *ret = nullptr;
  {
    auto *DerTy = cur ? dyn_cast<DIDerivedType>(cur->getBaseType())
                      : dyn_cast<DIDerivedType>(di_type);
    if (DerTy) {
      auto *baseType = DerTy->getBaseType();
      if (baseType) {
        if (baseType->getTag() == dwarf::DW_TAG_structure_type) {
          std::string typeName = baseType->getName().str();
          // errs() << "\t\tSTRUCT TYPE : " << typeName << "\n";
          ret = StructType::getTypeByName(*C, "struct." + typeName);
          // if (ret)
          //   ret->dump();
          // else
          //   errs() << "\t\t\tNO TYPE: " << typeName << "\n";
          /**
           * Structs can be defined and instantiated on the fly
           * EXAMPLE of a corner case:
           * static const struct {
           *   unsigned char flags;
           *   unsigned char flags;
           *   unsigned char combine;
           *   unsigned short end;
           * } ucnranges[] = {
           */

        } else if (baseType->getTag() == dwarf::DW_TAG_union_type) {
          // errs() << "\t\t UNION TYPE: " << baseType->getName().str() <<
          // "\n";
        } else if (baseType->getTag() == dwarf::DW_TAG_typedef) {
          // resolve the typedef, dump the type
          auto *derived = dyn_cast<DIDerivedType>(baseType);
          auto bt = derived->getBaseType();
          // errs() << "\t\tBASE TYPE (TYPEDEF): ";
          // bt->dump();
          if (bt->getTag() == dwarf::DW_TAG_structure_type) {
            std::string typeName = bt->getName().str();
            // errs() << "\t\tSTRUCT TYPE (TYPEDEF): " << typeName << "\n";
            ret = StructType::getTypeByName(*C, "struct." + typeName);
            // if (ret)
            //   ret->dump();
            // else
            // errs() << "\t\t\tNO TYPE: " << typeName << "\n";
          } else if (bt->getTag() == dwarf::DW_TAG_union_type) {
            // errs() << "\t\t UNION TYPE (TYPEDEF): " << bt->getName().str()
            //  << "\n";
          }
        }
      }
    }
  }
  // errs() << "END getStructTypeFromDbgInfo for GV " << GV->getName()
  //        << ", DEPTH: " << depth << "\n";
  if (numElements)
    *numElements = depth;
  return ret;
}

/** Only expect structs, arrays of structs, matrices of structs */
void HWAddressSanitizer::instrumentGlobal(GlobalVariable *GV) {
  Constant *Initializer = GV->getInitializer();
  Type *GVType = GV->getValueType();

  StructType *STType = nullptr;
  assert(GVType->isAggregateType() &&
         "[FSAN] Expected only aggregate types to be instrumented");

  uint64_t nElems = 1;
  uint64_t depth = 0;

  if (ArrayType *AT = dyn_cast<ArrayType>(GVType)) { // NEW
    auto InTY = AT->getElementType();
    nElems = AT->getNumElements();
    depth++;
    while (ArrayType *INAT = dyn_cast<ArrayType>(InTY)) {
      InTY = INAT->getElementType();
      nElems *= INAT->getNumElements();
      depth++;
    }
    assert(InTY->isStructTy() &&
           "[FSAN] Expected only arrays of structs to be instrumented");
    STType = dyn_cast<StructType>(InTY);
  } // if it's an array
  else if (StructType *ST = dyn_cast<StructType>(GVType)) {
    STType = ST;
  } else {
    assert(
        false &&
        "[FSAN] Expected only structs or arrays of structs to be instrumented");
  }
  Constant *ArraySize = ConstantInt::get(Int32Ty, nElems);

  if (STType->isLiteral()) {
    auto *tmp = getStructTypeFromDbgInfo(GV, nullptr, nullptr);
    if (tmp) {
      STType = tmp;
      if (STType->hasName() && STType->getName().str().find("union.") == 0)
        return; // skip unions
    } else
      return;
  }

  // if (depth > 0) {
  //   errs() << "[FSAN] TAG GV: " << GV->getName() << ", TY: " << *GVType <<
  //   "\n"; errs() << "\t * " << depth << "-D array of structs" << "\n"; errs()
  //   << "\t * Number of elements: " << nElems << "\n";
  // }

  // END of type check
  uint64_t SizeInBytes =
      M.getDataLayout().getTypeAllocSize(Initializer->getType());
  auto *NewGV = new GlobalVariable(M, Initializer->getType(), GV->isConstant(),
                                   GlobalValue::ExternalLinkage, Initializer,
                                   GV->getName() + ".hwasan");
  NewGV->copyAttributesFrom(GV);
  NewGV->setLinkage(GlobalValue::PrivateLinkage);
  NewGV->copyMetadata(GV, 0);
  auto *MD_node =
      MDNode::get(*C, ConstantAsMetadata::get(ConstantInt::get(Int32Ty, 1)));
  NewGV->setMetadata("fsan.instrument", MD_node);
  NewGV->setAlignment(
      std::max(GV->getAlign().valueOrOne(), Mapping.getObjectAlignment()));

  // It is invalid to ICF two globals that have different tags. In the case
  // where the size of the global is a multiple of the tag granularity the
  // contents of the globals may be the same but the tags (i.e. symbol
  // values) may be different, and the symbols are not considered during
  // ICF. In the case where the size is not a multiple of the granularity,
  // the short granule tags would discriminate two globals with different
  // tags, but there would otherwise be nothing stopping such a global from
  // being incorrectly ICF'd with an uninstrumented (i.e. tag 0) global that
  // happened to have the short granule tag in the last byte.
  NewGV->setUnnamedAddr(GlobalValue::UnnamedAddr::None);
  // NOTE: the new global is actually the symbol that gets loaded on each
  // use of the former global

  // NOTE: dont set tag vector here, do it once and for all in constructor
  // and only reference it here

  auto *DescriptorTy = StructType::get(
      Int32Ty, Int32Ty, Int32Ty,
      Int32Ty); // addr, info, tagvec ptr, n_elem if array or matrix
  const uint64_t MaxDescriptorSize = 0xfffff0;
  for (uint64_t DescriptorPos = 0; DescriptorPos < SizeInBytes;
       DescriptorPos += MaxDescriptorSize) {
    auto *Descriptor =
        new GlobalVariable(M, DescriptorTy, true, GlobalValue::PrivateLinkage,
                           nullptr, GV->getName() + ".hwasan.descriptor");
    auto *GVRelPtr = ConstantExpr::getTrunc(
        ConstantExpr::getAdd(
            ConstantExpr::getSub(
                ConstantExpr::getPtrToInt(NewGV, Int64Ty),
                ConstantExpr::getPtrToInt(Descriptor, Int64Ty)),
            ConstantInt::get(
                Int64Ty,
                DescriptorPos)), // NOTE: when descriptor pos is 0, omitted
        Int32Ty);

    assert(STType &&
           "Struct type must be valid to instrument global variable.");
    GlobalVariable *TagVector =
        dyn_cast<GlobalVariable>(RetrieveOrCreateTagVector(STType, M, depth));
    assert(TagVector &&
           "Tag vector global must exist and be properly initialized.");
    auto *TVRelPtr = ConstantExpr::getTrunc(
        ConstantExpr::getSub(ConstantExpr::getPtrToInt(TagVector, Int64Ty),
                             ConstantExpr::getPtrToInt(Descriptor, Int64Ty)),
        Int32Ty);
    assert(ArraySize && "Array size constant must be valid.");
    // uint32_t Size = std::min(SizeInBytes - DescriptorPos, MaxDescriptorSize);
    // auto *SizeAndTag = ConstantInt::get(Int32Ty, Size);
    auto *SizeOfTheStruct =
        ConstantInt::get(Int32Ty, M.getDataLayout().getTypeAllocSize(STType));
    Descriptor->setComdat(NewGV->getComdat());
    Descriptor->setInitializer(ConstantStruct::getAnon(
        {GVRelPtr, SizeOfTheStruct, TVRelPtr, ArraySize}));
    Descriptor->setSection("hwasan_globals");
    Descriptor->setMetadata(LLVMContext::MD_associated,
                            MDNode::get(*C, ValueAsMetadata::get(NewGV)));
    // Descriptor->setAlignment(Align(16)); // doesnt really matter
    appendToCompilerUsed(M, Descriptor);
  }
  uint8_t Tag = 0;
  Tag = RPTag; // NOTE: both structs and arrays of structs have RP set

  Constant *Aliasee = ConstantExpr::getIntToPtr(
      ConstantExpr::getAdd(
          ConstantExpr::getPtrToInt(NewGV, Int64Ty),
          ConstantInt::get(Int64Ty, (uint64_t)(Tag) << PointerTagShift)),
      GV->getType());
  auto *Alias = GlobalAlias::create(GV->getValueType(), GV->getAddressSpace(),
                                    GV->getLinkage(), "", Aliasee, &M);
  Alias->setVisibility(GV->getVisibility());
  Alias->takeName(GV);
  GV->replaceAllUsesWith(Alias);
  GV->eraseFromParent();
  NumInstrumentedGlobals++;
} // instrumentGlobal

void HWAddressSanitizer::instrumentGlobals() {
  std::vector<GlobalVariable *> Globals;
  for (GlobalVariable &GV : M.globals()) {
    if (GV.hasSanitizerMetadata() && GV.getSanitizerMetadata().NoHWAddress) {
      continue;
    }

    if (GV.isDeclarationForLinker() || GV.getName().starts_with("llvm.") ||
        GV.isThreadLocal())
      continue;

    // Common symbols can't have aliases point to them, so they can't be
    // tagged.
    if (GV.hasCommonLinkage())
      continue;
    /** NOTE: FSAN does not instrument tag vectors, they are special globals for
     * tagging */
    if (GV.getName().contains("tagvec"))
      continue;

    // Globals with custom sections may be used in __start_/__stop_
    // enumeration, which would be broken both by adding tags and
    // potentially by the extra padding/alignment that we insert.
    if (GV.hasSection())
      continue;

    if (GV.getValueType()->isArrayTy()) {
      Type *TY = dyn_cast<ArrayType>(GV.getValueType());

      while (ArrayType *AT = dyn_cast<ArrayType>(TY)) {
        TY = AT->getElementType();
      }

      if (!TY->isStructTy()) {
        continue;
      } else {
        auto ST = dyn_cast<StructType>(TY);
        if (ST->hasName() &&
            ST->getStructName().str().find("union.") != std::string::npos) {
          continue;
        }

      } // it's an array of structs
    } else if (GV.getValueType()->isStructTy()) {
      auto ST = dyn_cast<StructType>(GV.getValueType());
      if (ST->hasName() &&
          ST->getStructName().str().find("union.") != std::string::npos) {
        continue;
      }

    } else if (!GV.getValueType()->isStructTy()) {
      continue;
    }

    Globals.push_back(&GV);
  }
  // NOTE: I am assuming all the above checks are necessary.
  for (GlobalVariable *GV : Globals) {
    instrumentGlobal(GV);
  } // for global var
} // instrumentGlobals

// TODO: why do we even need this in first place?
void HWAddressSanitizer::instrumentPersonalityFunctions() {
  // We need to untag stack frames as we unwind past them. That is the job
  // of the personality function wrapper, which either wraps an existing
  // personality function or acts as a personality function on its own. Each
  // function that has a personality function or that can be unwound past
  // has its personality function changed to a thunk that calls the
  // personality function wrapper in the runtime.
  MapVector<Constant *, std::vector<Function *>> PersonalityFns;
  for (Function &F : M) {
    if (F.isDeclaration() || !F.hasFnAttribute(Attribute::SanitizeHWAddress))
      continue;

    if (F.hasPersonalityFn()) {
      PersonalityFns[F.getPersonalityFn()->stripPointerCasts()].push_back(&F);
    } else if (!F.hasFnAttribute(Attribute::NoUnwind)) {
      PersonalityFns[nullptr].push_back(&F);
    }
  }

  if (PersonalityFns.empty())
    return;

  FunctionCallee HwasanPersonalityWrapper = M.getOrInsertFunction(
      "__hwasan_personality_wrapper", Int32Ty, Int32Ty, Int32Ty, Int64Ty, PtrTy,
      PtrTy, PtrTy, PtrTy, PtrTy);
  FunctionCallee UnwindGetGR = M.getOrInsertFunction("_Unwind_GetGR", VoidTy);
  FunctionCallee UnwindGetCFA = M.getOrInsertFunction("_Unwind_GetCFA", VoidTy);

  for (auto &P : PersonalityFns) {
    std::string ThunkName = kHwasanPersonalityThunkName;
    if (P.first)
      ThunkName += ("." + P.first->getName()).str();
    FunctionType *ThunkFnTy = FunctionType::get(
        Int32Ty, {Int32Ty, Int32Ty, Int64Ty, PtrTy, PtrTy}, false);
    bool IsLocal = P.first && (!isa<GlobalValue>(P.first) ||
                               cast<GlobalValue>(P.first)->hasLocalLinkage());
    auto *ThunkFn = Function::Create(ThunkFnTy,
                                     IsLocal ? GlobalValue::InternalLinkage
                                             : GlobalValue::LinkOnceODRLinkage,
                                     ThunkName, &M);
    // TODO: think about other attributes as well.
    // if (any_of(P.second, [](const Function *F) {
    //       return F->hasFnAttribute("branch-target-enforcement");
    //     })) {
    //   ThunkFn->addFnAttr("branch-target-enforcement");
    // }
    if (!IsLocal) {
      ThunkFn->setVisibility(GlobalValue::HiddenVisibility);
      ThunkFn->setComdat(M.getOrInsertComdat(ThunkName));
    }

    auto *BB = BasicBlock::Create(*C, "entry", ThunkFn);
    IRBuilder<> IRB(BB);
    CallInst *WrapperCall = IRB.CreateCall(
        HwasanPersonalityWrapper,
        {ThunkFn->getArg(0), ThunkFn->getArg(1), ThunkFn->getArg(2),
         ThunkFn->getArg(3), ThunkFn->getArg(4),
         P.first ? P.first : Constant::getNullValue(PtrTy),
         UnwindGetGR.getCallee(), UnwindGetCFA.getCallee()});
    WrapperCall->setTailCall();
    IRB.CreateRet(WrapperCall);

    for (Function *F : P.second)
      F->setPersonalityFn(ThunkFn);
  }
}

void HWAddressSanitizer::ShadowMapping::init(Triple &TargetTriple,
                                             bool InstrumentWithCalls,
                                             bool CompileKernel) {
  // Start with defaults.
  Scale = kDefaultShadowScale;
  Kind = OffsetKind::kTls;
  WithFrameRecord = true;

  // // Tune for the target.
  // if (TargetTriple.isOSFuchsia()) {
  //   // Fuchsia is always PIE, which means that the beginning of the
  //   address
  //   // space is always available.
  //   SetFixed(0);
  // } else

  if (InstrumentWithCalls) {
    SetFixed(0);
    WithFrameRecord = false;
  }
  WithFrameRecord = optOr(ClFrameRecords, WithFrameRecord);

  // Apply the last of ClMappingOffset and ClMappingOffsetDynamic.
  Kind = optOr(ClMappingOffsetDynamic, Kind);
  if (ClMappingOffset.getNumOccurrences() > 0 &&
      !(ClMappingOffsetDynamic.getNumOccurrences() > 0 &&
        ClMappingOffsetDynamic.getPosition() > ClMappingOffset.getPosition())) {
    SetFixed(ClMappingOffset);
  }
}