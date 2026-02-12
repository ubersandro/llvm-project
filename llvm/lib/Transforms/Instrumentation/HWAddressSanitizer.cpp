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
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/DomTreeUpdater.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/Analysis/StackSafetyAnalysis.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TypeCopilot.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/BinaryFormat/ELF.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/MD5.h"
#include "llvm/Support/RandomNumberGenerator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Transforms/Instrumentation/AddressSanitizerCommon.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Instrumentation.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/MemoryTaggingSupport.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include <deque>
#include <optional>
#include <random>

using namespace llvm;

#define DEBUG_TYPE "hwasan"

const char kHwasanModuleCtorName[] = "hwasan.module_ctor";
const char kHwasanNoteName[] = "hwasan.note";
const char kHwasanInitName[] = "__hwasan_init";
const char kHwasanPersonalityThunkName[] = "__hwasan_personality_thunk";

const char kHwasanShadowMemoryDynamicAddress[] =
    "__hwasan_shadow_memory_dynamic_address";

// Accesses sizes are powers of two: 1, 2, 4, 8, 16.
static const size_t kNumberOfAccessSizes = 5;

static const size_t kDefaultShadowScale = 0; // 1 to 1 mapping in shadow memory

static const unsigned kShadowBaseAlignment = 32; // TODO: why is this unused?

namespace {
enum class OffsetKind {
  kFixed = 0,
  kGlobal,
  kIfunc,
  kTls,
};
}
/**
 * SW compatibility is a concern. When using un-instrumented code (e.g libs),
 * tagged pointers might wreak havoc.
 */
static cl::opt<std::string>
    ClMemoryAccessCallbackPrefix("hwasan-memory-access-callback-prefix",
                                 cl::desc("Prefix for memory access callbacks"),
                                 cl::Hidden, cl::init("__hwasan_"));

static cl::opt<bool> ClKasanMemIntrinCallbackPrefix(
    "hwasan-kernel-mem-intrinsic-prefix",
    cl::desc("Use prefix for memory intrinsics in KASAN mode"), cl::Hidden,
    cl::init(false));

static cl::opt<bool> ClInstrumentWithCalls(
    "hwasan-instrument-with-calls",
    cl::desc("instrument reads and writes with callbacks"), cl::Hidden,
    cl::init(true)); // HWAsanIO does this, no idea why - maybe debugging?

static cl::opt<bool> ClInstrumentReads("hwasan-instrument-reads",
                                       cl::desc("instrument read instructions"),
                                       cl::Hidden, cl::init(true));

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

static cl::opt<bool>
    ClRecover("hwasan-recover",
              cl::desc("Enable recovery mode (continue-after-error)."),
              cl::Hidden, cl::init(false)); // TODO: use for testing later

static cl::opt<bool> ClInstrumentStack("hwasan-instrument-stack",
                                       cl::desc("instrument stack (allocas)"),
                                       cl::Hidden, cl::init(true));

static cl::opt<bool> ClInstrumentPtrToInt(
    "fieldarmor-instrument-ptr-to-int",
    cl::desc("instrument stack ptrToInt instructions to untag results"),
    cl::Hidden, cl::init(true));

static cl::opt<bool> ClInstrumentGEPs(
    "fieldarmor-instrument-geps",
    cl::desc("instrument getelementptr instructions to untag results"),
    cl::Hidden, cl::init(true));

static cl::opt<bool> ClInstrumentArithmetic(
    "fieldarmor-instrument-arithmetic",
    cl::desc("instrument arithmetic instructions to untag results"), cl::Hidden,
    cl::init(true));

static cl::opt<bool>
    ClUseStackSafety("hwasan-use-stack-safety", cl::Hidden, cl::init(true),
                     cl::Hidden, cl::desc("Use Stack Safety analysis results"),
                     cl::Optional);

static cl::opt<size_t> ClMaxLifetimes(
    "hwasan-max-lifetimes-for-alloca", cl::Hidden, cl::init(3),
    cl::ReallyHidden,
    cl::desc("How many lifetime ends to handle for a single alloca."),
    cl::Optional);

static cl::opt<bool> ClGenerateTagsWithCalls(
    "hwasan-generate-tags-with-calls",
    cl::desc("generate new tags with runtime library calls"), cl::Hidden,
    cl::init(false));

static cl::opt<bool> ClGlobals("hwasan-globals", cl::desc("Instrument globals"),
                               cl::Hidden, cl::init(true));

static cl::opt<int> ClMatchAllTag(
    "hwasan-match-all-tag",
    cl::desc("don't report bad accesses via pointers with this tag"),
    cl::Hidden, cl::init(-1)); // TODO look into this, might come in very handy

static cl::opt<bool>
    ClEnableKhwasan("hwasan-kernel",
                    cl::desc("Enable KernelHWAddressSanitizer instrumentation"),
                    cl::Hidden, cl::init(false));

// These flags allow to change the shadow mapping and control how shadow memory
// is accessed. The shadow mapping looks like:
//    Shadow = (Mem >> scale) + offset

static cl::opt<uint64_t>
    ClMappingOffset("hwasan-mapping-offset",
                    cl::desc("HWASan shadow mapping offset [EXPERIMENTAL]"),
                    cl::Hidden);

static cl::opt<OffsetKind> ClMappingOffsetDynamic(
    "hwasan-mapping-offset-dynamic",
    cl::desc("HWASan shadow mapping dynamic offset location"), cl::Hidden,
    cl::values(clEnumValN(OffsetKind::kGlobal, "global", "Use global"),
               clEnumValN(OffsetKind::kIfunc, "ifunc", "Use ifunc global"),
               clEnumValN(OffsetKind::kTls, "tls", "Use TLS")));

static cl::opt<bool>
    ClFrameRecords("hwasan-with-frame-record",
                   cl::desc("Use ring buffer for stack allocations"),
                   cl::Hidden);

static cl::opt<int> ClHotPercentileCutoff("hwasan-percentile-cutoff-hot",
                                          cl::desc("Hot percentile cutoff."));

STATISTIC(NumTotalFuncs, "Number of total funcs");
STATISTIC(NumInstrumentedFuncs, "Number of instrumented funcs");
STATISTIC(NumNoProfileSummaryFuncs, "Number of funcs without PS");

// STATISTIC(NumTotalGEPs, "Number of total GEP instructions");
STATISTIC(
    NumUntaggedGEPResults,
    "Number of untagged GEP results"); // proxy for how many checks we skip
STATISTIC(NumInstrumentedGEPs, "Number of instrumented GEP instructions");
// STATISTIC(NumIgnoredGEPs, "Number of ignored GEP instructions");

STATISTIC(NumInstrumentedGlobals, "Number of instrumented global variables");
STATISTIC(NumDefinedTagVectors, "Number of defined tag vectors (same as the "
                                "number of totally identified struct types.)");
STATISTIC(NumInstrumentedCMPs, "Number of instrumented CMP instructions");
// STATISTIC(NumEmbeddedUnions, "Number of unions embedded in other structs");
// STATISTIC(NumLiteralStructs, "Number of literal structs encountered");
// STATISTIC(NumLiteralStructsEmbedded,
//           "Number of literal structs embedded in other structs");

// STATISTIC(NumInstrumentedArithmeticOps,
//           "Number of instrumented arithmetic instructions");
// STATISTIC(
//     NumChecksOnUntaggedPtrs,
//     "Number of checks skipped on untagged pointers"); // TODO: find a way of
//                                                       // implementing this.
//                                                       It's
//                                                       // impossible to get it
//                                                       // from the LOAD/STORE
//                                                       // instruction itself
STATISTIC(NumInstrumentedMemAccesses, "Number of instrumented memory accesses");
// Mode for selecting how to insert frame record info into the stack ring
// buffer.

enum RecordStackHistoryMode {
  // Do not record frame record info.
  none,

  // Insert instructions into the prologue for storing into the stack ring
  // buffer directly.
  instr,

  // Add a call to __hwasan_add_frame_record in the runtime.
  libcall,
};

static cl::opt<bool>
    ClInstrumentMemIntrinsics("hwasan-instrument-mem-intrinsics",
                              cl::desc("instrument memory intrinsics"),
                              cl::Hidden, cl::init(true));

static cl::opt<bool>
    ClInstrumentLandingPads("hwasan-instrument-landing-pads",
                            cl::desc("instrument landing pads"), cl::Hidden,
                            cl::init(false));

static cl::opt<bool> ClInstrumentPersonalityFunctions(
    "hwasan-instrument-personality-functions",
    cl::desc("instrument personality functions"),
    cl::Hidden); // ALE: why would I use this?

static cl::opt<bool> ClInlineAllChecks("hwasan-inline-all-checks",
                                       cl::desc("inline all checks"),
                                       cl::Hidden, cl::init(false));

static cl::opt<bool> ClInlineFastPathChecks("hwasan-inline-fast-path-checks",
                                            cl::desc("inline all checks"),
                                            cl::Hidden, cl::init(false));

namespace {

template <typename T> T optOr(cl::opt<T> &Opt, T Other) {
  return Opt.getNumOccurrences() ? Opt : Other;
}

bool shouldInstrumentStack(const Triple &TargetTriple) {
  return ClInstrumentStack;
}

bool shouldInstrumentWithCalls(const Triple &TargetTriple) {
  return optOr(ClInstrumentWithCalls, TargetTriple.getArch() == Triple::x86_64);
}

bool mightUseStackSafetyAnalysis(bool DisableOptimization) {
  return optOr(ClUseStackSafety, !DisableOptimization);
}

bool shouldUseStackSafetyAnalysis(const Triple &TargetTriple,
                                  bool DisableOptimization) {
  return shouldInstrumentStack(TargetTriple) &&
         mightUseStackSafetyAnalysis(DisableOptimization);
}

/// An instrumentation pass implementing detection of addressability bugs
/// using tagged pointers.
class HWAddressSanitizer {
public:
  HWAddressSanitizer(Module &M, bool CompileKernel, bool Recover,
                     const StackSafetyGlobalInfo *SSI,
                     const TypeCopilotResult *RetrievedTypes)
      : M(M), SSI(SSI), RetrievedTypes(RetrievedTypes) {
    this->Recover = optOr(ClRecover, Recover);
    this->CompileKernel =
        optOr(ClEnableKhwasan, CompileKernel); // TODO: remove later

    initializeModule(); // globals are initialized in here at some point.
    // TODO: introduce new analysis for heap, I need to be able to run it from
    // whatever LLVM pass at whatever point of the optimization pipeline
  }

  void sanitizeFunction(Function &F, FunctionAnalysisManager &FAM);

private:
  struct ShadowTagCheckInfo {
    Instruction *TagMismatchTerm = nullptr;
    Value *PtrLong = nullptr;
    Value *AddrLong = nullptr;
    Value *PtrTag = nullptr;
    Value *MemTag = nullptr;
  };

  // FieldArmor addenda
  // u_int64_t TagBits = 7; // for later use
  u_int64_t RPTag = 0x0LU;
  // it seems that setting RPTag to 0x80/0x40 breaks things in the C++ stdlib
  // TODO: look more into this -> there still things that do not make much
  // sense. For instance, GEPs and arithmetic clash
  // TODO: dump all the malloc happening, see if the size is influenced by GEPs
  // being tagged (and it will be for sure)
  // u_int64_t TagMask = 0b01111111Lu; // mask to apply to get T+L+R
  u_int64_t R_Mask = 0b01000000Lu;
  u_int64_t L_Mask = 0b00110000Lu;
  u_int64_t T_Mask = 0b00001111Lu;

  Value *T_Mask_value = nullptr;
  Value *L_Mask_value = nullptr;
  Value *R_Mask_value = nullptr;

  void InstrumentGEP(GetElementPtrInst *GEPI);
  void PreprocessGEP(GetElementPtrInst *GEPI);
  void InstrumentStoreOfFunctionArg(StoreInst *SI);
  Type *figureOutInheritance(const std::set<Type *> &structTypes);

  void TagAllocChunksBeforeUse(CallInst *CI,
                               const std::string &DemangledName); // FieldArmor
  void HandleNewOperator(CallInst *CI,
                         const std::string &DemangledName); // FieldArmor
  Value *GetArraySize(CallInst *CI, StructType *t,
                      IRBuilder<> &IRB); // FieldArmor
  void handleGEP2operands(GetElementPtrInst *GEPI);
  void InstrumentCMP(CmpInst *CI);
  void InstrumentPtrToInt(PtrToIntInst *PI);
  void InstrumentArithmetic(BinaryOperator *BO);
  void InstrumentConstGEP(ConstantExpr *GEPI);
  Value *getRPTag(IRBuilder<> &IRB); // FieldArmor
  Value *ApplyRLT(IRBuilder<> &IRB, Instruction *AI, Type *rootType,
                  const DataLayout &DL); // TODO: refactor remove DL

  u_int8_t *computeTags(StructType *t);           // FieldArmor
  void createTagVectors();                        // FieldArmor
  void createTagVector(StructType *t);            // FieldArmor
  bool potentiallyBlacklistFunction(Function &F); // FieldArmor
  // END FieldArmor

  bool selectiveInstrumentationShouldSkip(Function &F,
                                          FunctionAnalysisManager &FAM) const;
  void initializeModule();
  void createHwasanCtorComdat();

  void initializeCallbacks(Module &M);

  Value *getOpaqueNoopCast(IRBuilder<> &IRB,
                           Value *Val); // TODO: explore why this is needed

  Value *getDynamicShadowIfunc(IRBuilder<> &IRB);
  Value *getShadowNonTls(IRBuilder<> &IRB);

  void untagPointerOperand(Instruction *I, Value *Addr);
  Value *memToShadow(Value *Shadow, IRBuilder<> &IRB);

  int64_t getAccessInfo(bool IsWrite, unsigned AccessSizeIndex);
  ShadowTagCheckInfo insertShadowTagCheck(
      Value *Ptr, Instruction *InsertBefore, DomTreeUpdater &DTU,
      LoopInfo *LI); // this is for fast checking ... TODO Look into it
  void instrumentMemAccessOutline(Value *Ptr, bool IsWrite,
                                  unsigned AccessSizeIndex,
                                  Instruction *InsertBefore,
                                  DomTreeUpdater &DTU, LoopInfo *LI);
  void instrumentMemAccessInline(Value *Ptr, bool IsWrite,
                                 unsigned AccessSizeIndex,
                                 Instruction *InsertBefore, DomTreeUpdater &DTU,
                                 LoopInfo *LI);
  bool ignoreMemIntrinsic(OptimizationRemarkEmitter &ORE, MemIntrinsic *MI);
  void instrumentMemIntrinsic(MemIntrinsic *MI);
  bool instrumentMemAccess(InterestingMemoryOperand &O, DomTreeUpdater &DTU,
                           LoopInfo *LI, const DataLayout &DL);
  bool ignoreAccessWithoutRemark(Instruction *Inst, Value *Ptr);
  bool ignoreAccess(OptimizationRemarkEmitter &ORE, Instruction *Inst,
                    Value *Ptr);

  void getInterestingMemoryOperands(
      OptimizationRemarkEmitter &ORE, Instruction *I,
      const TargetLibraryInfo &TLI,
      SmallVectorImpl<InterestingMemoryOperand> &Interesting);

  void tagAlloca(IRBuilder<> &IRB, AllocaInst *AI, const DataLayout &DL);
  void untagAlloca(IRBuilder<> &IRB, AllocaInst *AI, const DataLayout &DL);
  Value *tagPointer(IRBuilder<> &IRB, Type *Ty, Value *PtrLong, Value *Tag);
  Value *untagPointer(IRBuilder<> &IRB, Value *PtrLong);
  bool instrumentStack(memtag::StackInfo &Info, const DominatorTree &DT,
                       const PostDominatorTree &PDT, const LoopInfo &LI,
                       const DataLayout &DL);
  bool instrumentLandingPads(SmallVectorImpl<Instruction *> &RetVec);
  Value *getNextTagWithCall(IRBuilder<> &IRB); // not sure I still need this

  Value *getHwasanThreadSlotPtr(IRBuilder<> &IRB);
  Value *applyTagMask(IRBuilder<> &IRB, Value *OldTag);
  unsigned retagMask(unsigned AllocaNo);

  // void emitPrologue(IRBuilder<> &IRB, bool WithFrameRecord); // TODO: do I
  // still need this?

  void instrumentGlobal(GlobalVariable *GV);

  void instrumentGlobals();

  Value *getCachedFP(IRBuilder<> &IRB);
  Value *getFrameRecordInfo(IRBuilder<> &IRB);

  void instrumentPersonalityFunctions();

  LLVMContext *C;
  Module &M;
  const StackSafetyGlobalInfo *SSI;
  const TypeCopilotResult *RetrievedTypes;
  Triple TargetTriple;

  /// This struct defines the shadow mapping using the rule:
  /// If `kFixed`, then
  ///   shadow = (mem >> Scale) + Offset.
  /// If `kGlobal`, then
  ///   extern char* __hwasan_shadow_memory_dynamic_address;
  ///   shadow = (mem >> Scale) + __hwasan_shadow_memory_dynamic_address
  /// If `kIfunc`, then
  ///   extern char __hwasan_shadow[];
  ///   shadow = (mem >> Scale) + &__hwasan_shadow
  /// If `kTls`, then
  ///   extern char *__hwasan_tls ; // THIS IS USED BY DEFAULT @ale
  ///   shadow = (mem>>Scale) + align_up(__hwasan_shadow, kShadowBaseAlignment)
  ///
  /// If WithFrameRecord is true, then __hwasan_tls will be used to access the
  /// ring buffer for storing stack allocations on targets that support it.
  class ShadowMapping {
    OffsetKind Kind;
    uint64_t Offset;
    uint8_t Scale;
    bool WithFrameRecord;

    void SetFixed(uint64_t O) {
      Kind = OffsetKind::kFixed;
      Offset = O;
    }

  public:
    void init(Triple &TargetTriple, bool InstrumentWithCalls,
              bool CompileKernel);
    Align getObjectAlignment() const { return Align(1ULL << Scale); }

    bool isInGlobal() const { return Kind == OffsetKind::kGlobal; }
    bool isInIfunc() const { return Kind == OffsetKind::kIfunc; }
    bool isInTls() const { return Kind == OffsetKind::kTls; }
    bool isFixed() const { return Kind == OffsetKind::kFixed; }
    uint8_t scale() const { return Scale; };
    uint64_t offset() const {
      assert(isFixed());
      return Offset;
    };
    bool withFrameRecord() const { return WithFrameRecord; };
  };

  ShadowMapping Mapping;

  Type *VoidTy = Type::getVoidTy(M.getContext());
  Type *IntptrTy = M.getDataLayout().getIntPtrType(M.getContext());
  PointerType *PtrTy = PointerType::getUnqual(M.getContext());
  Type *Int8Ty = Type::getInt8Ty(M.getContext());
  Type *Int32Ty = Type::getInt32Ty(M.getContext());
  Type *Int64Ty = Type::getInt64Ty(M.getContext());

  bool CompileKernel;
  bool Recover;
  bool OutlinedChecks;
  bool InlineFastPath;
  bool InstrumentLandingPads;
  bool InstrumentWithCalls;
  bool InstrumentStack;
  bool InstrumentGlobals;
  bool UseMatchAllCallback;

  std::optional<uint8_t> MatchAllTag;

  unsigned PointerTagShift;
  uint64_t TagMaskByte;

  Function *HwasanCtorFunction;

  FunctionCallee HwasanMemoryAccessCallback[2][kNumberOfAccessSizes];
  FunctionCallee HwasanMemoryAccessCallbackSized[2];

  FunctionCallee HwasanMemmove, HwasanMemcpy, HwasanMemset;
  FunctionCallee HwasanHandleVfork;

  FunctionCallee HwasanTagMemoryFunc;
  FunctionCallee HwasanGenerateTagFunc;
  FunctionCallee HwasanRecordFrameRecordFunc;

  Constant *ShadowGlobal;

  Value *ShadowBase = nullptr;

  Value *CachedFP = nullptr;
  GlobalValue *ThreadPtrGlobal = nullptr;
};

} // end anonymous namespace

PreservedAnalyses HWAddressSanitizerPass::run(Module &M,
                                              ModuleAnalysisManager &MAM) {
  // Return early if nosanitize_hwaddress module flag is present for the module.
  if (checkIfAlreadyInstrumented(M, "nosanitize_hwaddress"))
    return PreservedAnalyses::all();
  const StackSafetyGlobalInfo *SSI = nullptr;
  const TypeCopilotResult *RetrievedTypes = nullptr;
  MAM.registerPass([&] {
    return TypeReconstructionAnalysis();
  }); // TODO: this does not go here!
  RetrievedTypes = &MAM.getResult<TypeReconstructionAnalysis>(M);
  const Triple &TargetTriple = M.getTargetTriple();
  // TODO: investigate this, what if it hides UB?
  if (shouldUseStackSafetyAnalysis(TargetTriple, Options.DisableOptimization))
    SSI = &MAM.getResult<StackSafetyGlobalAnalysis>(M);

  HWAddressSanitizer HWASan(M, Options.CompileKernel, Options.Recover, SSI,
                            RetrievedTypes);
  auto &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

  for (Function &F : M) {

    // errs() << "=== HWASan Before Function: " << F.getName() << " ===\n";
    // F.print(errs());
    HWASan.sanitizeFunction(F, FAM);

    // errs() << "=== HWASan After Function: " << F.getName() << " ===\n";
    // F.print(errs());
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

  // x86_64 currently has two modes:
  // - Intel LAM (default)
  // - pointer aliasing (heap only)
  bool IsX86_64 = TargetTriple.getArch() == Triple::x86_64;

  InstrumentWithCalls = shouldInstrumentWithCalls(TargetTriple);
  InstrumentStack = shouldInstrumentStack(TargetTriple);

  PointerTagShift = IsX86_64 ? 57 : 56;
  TagMaskByte = IsX86_64 ? 0x3F : 0xFF;

  Mapping.init(TargetTriple, InstrumentWithCalls, CompileKernel);

  C = &(M.getContext());
  IRBuilder<> IRB(*C);

  HwasanCtorFunction = nullptr;

  // Older versions of Android do not have the required runtime support for
  // short granules, global or personality function instrumentation. On other
  // platforms we currently require using the latest version of the runtime.
  bool NewRuntime =
      !TargetTriple.isAndroid() || !TargetTriple.isAndroidVersionLT(30);

  OutlinedChecks = (TargetTriple.isAArch64() || TargetTriple.isRISCV64()) &&
                   TargetTriple.isOSBinFormatELF() &&
                   !optOr(ClInlineAllChecks, Recover);

  // These platforms may prefer less inlining to reduce binary size.
  InlineFastPath = optOr(ClInlineFastPathChecks, !(TargetTriple.isAndroid() ||
                                                   TargetTriple.isOSFuchsia()));

  if (ClMatchAllTag.getNumOccurrences()) {
    if (ClMatchAllTag != -1) {
      MatchAllTag = ClMatchAllTag & 0xFF;
    }
  } else if (CompileKernel) {
    MatchAllTag = 0xFF;
  }
  UseMatchAllCallback = !CompileKernel && MatchAllTag.has_value();

  // If we don't have personality function support, fall back to landing pads.
  InstrumentLandingPads = optOr(ClInstrumentLandingPads, !NewRuntime);

  InstrumentGlobals = !CompileKernel && optOr(ClGlobals, NewRuntime);

  if (!CompileKernel) {
    createHwasanCtorComdat(); // creates the routine ctor with a call into the
                              // runtime function __hwasan_init

    createTagVectors();
    if (InstrumentGlobals)
      instrumentGlobals();
    // TODO: bring back

    bool InstrumentPersonalityFunctions =
        optOr(ClInstrumentPersonalityFunctions, NewRuntime);
    if (InstrumentPersonalityFunctions)
      instrumentPersonalityFunctions();
  }

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
  T_Mask_value = ConstantInt::get(Type::getInt64Ty(M.getContext()), T_Mask);
  L_Mask_value = ConstantInt::get(Type::getInt64Ty(M.getContext()), L_Mask);
  R_Mask_value = ConstantInt::get(Type::getInt64Ty(M.getContext()), R_Mask);
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
    const std::string EndingStr = Recover ? "_noabort" : "";

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

void dbgPrintStructType(StructType *t) {
  bool isUnion = false;
  bool isLiteral = t->isLiteral();
  bool isOpaque = t->isOpaque();
  bool isSized = t->isSized();

  isUnion =
      !isLiteral && t->getName().str().find("union.") != std::string::npos;
  LLVM_DEBUG(dbgs() << "[FieldArmor - createTagVectors] Identified struct: "
                    << t->getName() << "\n");
  LLVM_DEBUG(dbgs() << "\t\ttype: ");
  LLVM_DEBUG(t->print(dbgs()));
  LLVM_DEBUG(dbgs() << "\n");
  LLVM_DEBUG(dbgs() << "\t\tisLiteral: " << isLiteral << "\n");
  LLVM_DEBUG(dbgs() << "\t\tisOpaque: " << isOpaque << "\n");
  LLVM_DEBUG(dbgs() << "\t\tisSized: " << isSized << "\n");
  LLVM_DEBUG(dbgs() << "\t\tisUnion: " << isUnion << "\n");
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
  // Mem >> Scale NOT ANYMORE
  // Value *Shadow = IRB.CreateLShr(Mem, Mapping.scale());
  // if (Mapping.isFixed() && Mapping.offset() == 0)
  //   return IRB.CreateIntToPtr(Shadow, PtrTy);
  // // (Mem >> Scale) + Offset
  // return IRB.CreatePtrAdd(ShadowBase, Shadow);
  // NEW
  // CURRENT: mem ^ 0x400000000000
  Value *XorVal =
      IRB.CreateXor(Mem, ConstantInt::get(IntptrTy, 0x400000000000ULL));
  return IRB.CreateIntToPtr(XorVal, PtrTy);
}

int64_t HWAddressSanitizer::getAccessInfo(bool IsWrite,
                                          unsigned AccessSizeIndex) {
  return (CompileKernel << HWASanAccessInfo::CompileKernelShift) |
         (MatchAllTag.has_value() << HWASanAccessInfo::HasMatchAllShift) |
         (MatchAllTag.value_or(0) << HWASanAccessInfo::MatchAllShift) |
         (Recover << HWASanAccessInfo::RecoverShift) |
         (IsWrite << HWASanAccessInfo::IsWriteShift) |
         (AccessSizeIndex << HWASanAccessInfo::AccessSizeShift);
}

HWAddressSanitizer::ShadowTagCheckInfo
HWAddressSanitizer::insertShadowTagCheck(Value *Ptr, Instruction *InsertBefore,
                                         DomTreeUpdater &DTU, LoopInfo *LI) {
  ShadowTagCheckInfo R;

  IRBuilder<> IRB(InsertBefore);

  R.PtrLong = IRB.CreatePointerCast(Ptr, IntptrTy);
  R.PtrTag =
      IRB.CreateTrunc(IRB.CreateLShr(R.PtrLong, PointerTagShift), Int8Ty);
  R.AddrLong = untagPointer(IRB, R.PtrLong);
  Value *Shadow = memToShadow(R.AddrLong, IRB);
  R.MemTag = IRB.CreateLoad(Int8Ty, Shadow);
  Value *TagMismatch = IRB.CreateICmpNE(R.PtrTag, R.MemTag);

  if (MatchAllTag.has_value()) {
    LLVM_DEBUG(dbgs() << "Inserting match-all tag check for tag="
                      << (unsigned)(*MatchAllTag) << "\n");
    Value *TagNotIgnored = IRB.CreateICmpNE(
        R.PtrTag, ConstantInt::get(R.PtrTag->getType(), *MatchAllTag));
    TagMismatch = IRB.CreateAnd(TagMismatch, TagNotIgnored);
  }

  R.TagMismatchTerm = SplitBlockAndInsertIfThen(
      TagMismatch, InsertBefore, false,
      MDBuilder(*C).createUnlikelyBranchWeights(), &DTU, LI);

  return R;
}

void HWAddressSanitizer::instrumentMemAccessOutline(Value *Ptr, bool IsWrite,
                                                    unsigned AccessSizeIndex,
                                                    Instruction *InsertBefore,
                                                    DomTreeUpdater &DTU,
                                                    LoopInfo *LI) {

  const int64_t AccessInfo = getAccessInfo(IsWrite, AccessSizeIndex);
  LLVM_DEBUG(dbgs() << "REMOVING INLINE CHECKS SINCE THEY BREAK EVERYTHING\n");

  // if (InlineFastPath) // @ale: this function short circuits checks if
  // inlineFastPath is true
  //   InsertBefore =
  //       insertShadowTagCheck(Ptr, InsertBefore, DTU, LI).TagMismatchTerm; //
  //       DONT DONT DONT

  IRBuilder<> IRB(InsertBefore);
  bool UseFixedShadowIntrinsic = false; // TODO: properly fix this @ale
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

  if (UseFixedShadowIntrinsic) { /* THIS IS STILL A MISTERY TO DATE */
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

  const int64_t AccessInfo = getAccessInfo(IsWrite, AccessSizeIndex);

  ShadowTagCheckInfo TCI = insertShadowTagCheck(Ptr, InsertBefore, DTU, LI);

  IRBuilder<> IRB(TCI.TagMismatchTerm);
  Value *OutOfShortGranuleTagRange =
      IRB.CreateICmpUGT(TCI.MemTag, ConstantInt::get(Int8Ty, 15));
  Instruction *CheckFailTerm = SplitBlockAndInsertIfThen(
      OutOfShortGranuleTagRange, TCI.TagMismatchTerm, !Recover,
      MDBuilder(*C).createUnlikelyBranchWeights(), &DTU, LI);

  IRB.SetInsertPoint(TCI.TagMismatchTerm);
  Value *PtrLowBits = IRB.CreateTrunc(IRB.CreateAnd(TCI.PtrLong, 15), Int8Ty);
  PtrLowBits = IRB.CreateAdd(
      PtrLowBits, ConstantInt::get(Int8Ty, (1 << AccessSizeIndex) - 1));
  Value *PtrLowBitsOOB = IRB.CreateICmpUGE(PtrLowBits, TCI.MemTag);
  SplitBlockAndInsertIfThen(PtrLowBitsOOB, TCI.TagMismatchTerm, false,
                            MDBuilder(*C).createUnlikelyBranchWeights(), &DTU,
                            LI, CheckFailTerm->getParent());

  IRB.SetInsertPoint(TCI.TagMismatchTerm);
  Value *InlineTagAddr = IRB.CreateOr(TCI.AddrLong, 15);
  InlineTagAddr = IRB.CreateIntToPtr(InlineTagAddr, PtrTy);
  Value *InlineTag = IRB.CreateLoad(Int8Ty, InlineTagAddr);
  Value *InlineTagMismatch = IRB.CreateICmpNE(TCI.PtrTag, InlineTag);
  SplitBlockAndInsertIfThen(InlineTagMismatch, TCI.TagMismatchTerm, false,
                            MDBuilder(*C).createUnlikelyBranchWeights(), &DTU,
                            LI, CheckFailTerm->getParent());

  IRB.SetInsertPoint(CheckFailTerm);
  InlineAsm *Asm;
  switch (TargetTriple.getArch()) {
  case Triple::x86_64:
    // The signal handler will find the data address in rdi.
    Asm = InlineAsm::get(
        FunctionType::get(VoidTy, {TCI.PtrLong->getType()}, false),
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
        FunctionType::get(VoidTy, {TCI.PtrLong->getType()}, false),
        "brk #" + itostr(0x900 + (AccessInfo & HWASanAccessInfo::RuntimeMask)),
        "{x0}",
        /*hasSideEffects=*/true);
    break;
  case Triple::riscv64:
    // The signal handler will find the data address in x10.
    Asm = InlineAsm::get(
        FunctionType::get(VoidTy, {TCI.PtrLong->getType()}, false),
        "ebreak\naddiw x0, x11, " +
            itostr(0x40 + (AccessInfo & HWASanAccessInfo::RuntimeMask)),
        "{x10}",
        /*hasSideEffects=*/true);
    break;
  default:
    report_fatal_error("unsupported architecture");
  }
  IRB.CreateCall(Asm, TCI.PtrLong);
  if (Recover)
    cast<BranchInst>(CheckFailTerm)
        ->setSuccessor(0, TCI.TagMismatchTerm->getParent());
}

bool HWAddressSanitizer::ignoreMemIntrinsic(OptimizationRemarkEmitter &ORE,
                                            MemIntrinsic *MI) {
  if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(MI)) {
    return (!ClInstrumentWrites || ignoreAccess(ORE, MTI, MTI->getDest())) &&
           (!ClInstrumentReads || ignoreAccess(ORE, MTI, MTI->getSource()));
  }
  if (isa<MemSetInst>(MI))
    return !ClInstrumentWrites || ignoreAccess(ORE, MI, MI->getDest());
  return false;
}

void HWAddressSanitizer::instrumentMemIntrinsic(MemIntrinsic *MI) {
  /** TODO: just instrument intrinsics that operate on non-root ptrs. Ideally,
   * we want to start catching memcpys on pointers to fields that overwrite the
   * whole struct or parts of it. */
  IRBuilder<> IRB(MI);

  if (isa<MemTransferInst>(MI)) { /*memcpy, memmove*/
    SmallVector<Value *, 4> Args{
        MI->getOperand(0), MI->getOperand(1),
        IRB.CreateIntCast(MI->getOperand(2), IntptrTy, false)};

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
  // 2) the shadow memory corresponding to address 0 is initialized to zero and
  //    never updated.
  // We can therefore elide the tag check.
  llvm::KnownBits Known(DL.getPointerTypeSizeInBits(Addr->getType()));
  llvm::computeKnownBits(Addr, Known, DL);
  if (Known.isZero()) {
    // errs() << "[FieldArmor] Skipping instrumentation of null pointer
    // access\n"; errs() << "\t\t\tInstruction: " << *(O.getInsn()) << "\n";
    return false;
  }

  if (O.MaybeMask)
    return false; // FIXME
  // WHAT IS THIS?

  IRBuilder<> IRB(O.getInsn());
  if (!O.TypeStoreSize.isScalable() && isPowerOf2_64(O.TypeStoreSize) &&
      (O.TypeStoreSize / 8 <= (1ULL << (kNumberOfAccessSizes - 1))) &&
      (!O.Alignment || *O.Alignment >= Mapping.getObjectAlignment() ||
       *O.Alignment >= O.TypeStoreSize / 8)) {
    size_t AccessSizeIndex = TypeSizeToSizeIndex(O.TypeStoreSize);

    SmallVector<Value *, 2> Args{IRB.CreatePointerCast(Addr, IntptrTy)};
    IRB.CreateCall(HwasanMemoryAccessCallback[O.IsWrite][AccessSizeIndex],
                   Args);

  } else {
    SmallVector<Value *, 3> Args{
        IRB.CreatePointerCast(Addr, IntptrTy),
        IRB.CreateUDiv(IRB.CreateTypeSize(IntptrTy, O.TypeStoreSize),
                       ConstantInt::get(IntptrTy, 8))};
    IRB.CreateCall(HwasanMemoryAccessCallbackSized[O.IsWrite], Args);
  }
  untagPointerOperand(
      O.getInsn(), Addr); // This is the right way of handling pointer operands
  NumInstrumentedMemAccesses++;
  return true;
}

/**
 * Applies RLT to memory
 */
Value *HWAddressSanitizer::ApplyRLT(IRBuilder<> &IRB, Instruction *AI,
                                    Type *rootType, const DataLayout &DL) {

  auto structTy = cast<StructType>(rootType);
  auto tagVector = M.getGlobalVariable(
      structTy->getStructName().str() + ".fieldarmor.tagvec", true);

  if (!tagVector) {
    createTagVector(structTy);
  }
  // TODO: pointer must be untagged. Why is it tagged?
  tagVector = M.getGlobalVariable(
      structTy->getStructName().str() + ".fieldarmor.tagvec", true);
  assert(tagVector && "Tag vector must exist here - tagAlloca");
  FunctionCallee fieldarmor_tag_memory =
      M.getOrInsertFunction("_ZN8__hwasan21fieldarmor_tag_memoryEPvmm", PtrTy,
                            PtrTy, PtrTy, Int64Ty, Int64Ty);
  // IRB.SetInsertPoint(AI->getNextNode()); // what if I ignore this?

  return IRB.CreateCall(
      fieldarmor_tag_memory,
      {IRB.CreatePointerCast(AI, PtrTy),
       IRB.CreatePointerCast(tagVector, PtrTy),
       ConstantInt::get(Int64Ty, DL.getTypeAllocSize(rootType)),
       ConstantInt::get(Int64Ty, 1)});

} // ApplyRLT

void HWAddressSanitizer::untagAlloca(IRBuilder<> &IRB, AllocaInst *AI,
                                     const DataLayout &DL) {
  /** Apply tag 0 to the previously tagged memory, immaterially of the type. */
  FunctionCallee fieldarmor_tag_memory =
      M.getOrInsertFunction("_ZN8__hwasan21fieldarmor_tag_memoryEPvmm", PtrTy,
                            PtrTy, PtrTy, Int64Ty, Int64Ty);
  Value *NullTagVector = IRB.CreateIntToPtr(ConstantInt::get(IntptrTy, 0),
                                            PtrTy); // all zeroes tag vector
  IRB.CreateCall(
      fieldarmor_tag_memory,
      {IRB.CreatePointerCast(AI, PtrTy), NullTagVector,
       ConstantInt::get(Int64Ty, DL.getTypeAllocSize(AI->getAllocatedType())),
       ConstantInt::get(Int64Ty, 1)});

} // untagAlloca

// TODO: correctly handle aggregates of vectors
void HWAddressSanitizer::tagAlloca(IRBuilder<> &IRB, AllocaInst *AI,
                                   const DataLayout &DL) {
  if (StructType *ST = dyn_cast<StructType>(AI->getAllocatedType())) {
    ApplyRLT(IRB, AI, ST, DL);
  } // StructType

  else if (VectorType *VT = dyn_cast<VectorType>(AI->getAllocatedType())) {
    errs() << "[FieldArmor] WARNING: Alloca of VectorType for RLT not yet "
              "supported: "
           << *(VT) << "\n";
  } // VectorType

  else if (ArrayType *AT = dyn_cast<ArrayType>(AI->getAllocatedType())) {
    auto elementType = AT->getElementType();

    if (elementType->isStructTy()) {
      for (u_int64_t el = 0; el < AT->getNumElements(); el++) {
        auto *ElementPtr =
            IRB.CreateGEP(elementType, AI, {ConstantInt::get(Int64Ty, el)});
        GetElementPtrInst *GepInstruction = cast<GetElementPtrInst>(ElementPtr);
        ApplyRLT(IRB, GepInstruction, elementType, DL);
      } // for
    } // CASE: ARRAY OF STRUCTS

    else if (elementType->isArrayTy()) {
      // NOTE: SPEC2017 does not use arrays of arrays, apparently
      errs() << "[FieldArmor] Alloca of array of arrays "
             << *(AI->getAllocatedType()) << "\n";
      for (u_int64_t el = 0; el < AT->getNumElements(); el++) {
        auto *ElementPtr =
            IRB.CreateGEP(elementType, AI, {ConstantInt::get(Int64Ty, el)});
        // this points to an array
        GetElementPtrInst *i_th_array = cast<GetElementPtrInst>(ElementPtr);
        ArrayType *innerArrayType = cast<ArrayType>(elementType);
        auto int_n = innerArrayType->getNumElements();
        for (uint64_t el_int = 0; el_int < int_n; el_int++) {
          auto *innerElementPtr =
              IRB.CreateGEP(innerArrayType->getElementType(), i_th_array,
                            {ConstantInt::get(Int64Ty, el_int)});
          GetElementPtrInst *GepInstruction =
              cast<GetElementPtrInst>(innerElementPtr);
          ApplyRLT(IRB, GepInstruction, innerArrayType->getElementType(), DL);
        } // for inner elements
      } // for each element, tag
    } // CASE: ARRAY OF ARRAYS
  } // ArrayType
  else {
    // SPEC2017 never hits this case
    errs() << "[FieldArmor] WARNING: Alloca of unsupported type for RLT: "
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

Value *HWAddressSanitizer::applyTagMask(IRBuilder<> &IRB, Value *OldTag) {
  if (TagMaskByte == 0xFF)
    return OldTag; // No need to clear the tag byte.
  return IRB.CreateAnd(OldTag,
                       ConstantInt::get(OldTag->getType(), TagMaskByte));
}

Value *HWAddressSanitizer::getNextTagWithCall(IRBuilder<> &IRB) {
  return IRB.CreateZExt(IRB.CreateCall(HwasanGenerateTagFunc), IntptrTy);
}

// Add a tag to an address.
Value *HWAddressSanitizer::tagPointer(IRBuilder<> &IRB, Type *Ty,
                                      Value *PtrLong, Value *Tag) {

  Value *TaggedPtrLong;
  Value *ShiftedTag = IRB.CreateShl(Tag, PointerTagShift);
  ShiftedTag->setName("ShiftedTag");
  TaggedPtrLong = IRB.CreateOr(PtrLong, ShiftedTag);
  TaggedPtrLong->setName("TaggedPtrLong");
  return IRB.CreateIntToPtr(TaggedPtrLong, Ty);
}

// Remove tag from an address.
inline Value *HWAddressSanitizer::untagPointer(IRBuilder<> &IRB,
                                               Value *PtrLong) {

  Value *UntaggedPtrLong;
  if (CompileKernel) {
    // Kernel addresses have 0xFF in the most significant byte.
    UntaggedPtrLong =
        IRB.CreateOr(PtrLong, ConstantInt::get(PtrLong->getType(),
                                               TagMaskByte << PointerTagShift));
  } else {
    // Userspace addresses have 0x00.
    UntaggedPtrLong = IRB.CreateAnd(
        PtrLong, ConstantInt::get(PtrLong->getType(),
                                  ~(TagMaskByte << PointerTagShift)));
  }
  return UntaggedPtrLong;
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
  for (auto *LP : LandingPadVec) {
    IRBuilder<> IRB(LP->getNextNonDebugInstruction());
    IRB.CreateCall(
        HwasanHandleVfork,
        {memtag::readRegister(
            IRB, (TargetTriple.getArch() == Triple::x86_64) ? "rsp" : "sp")});
  }
  return true;
}

// the recall of the following methods is bad, but at least SPEC does not crash!
/** Filter out GEPs on structs based on the type of the struct. */
bool shouldBlocklistGEP(GetElementPtrInst *GEPI) {
  auto fatherType = GEPI->getSourceElementType();
  if (fatherType->isStructTy()) {
    StructType *ST = dyn_cast<StructType>(fatherType);
    if (!ST->isLiteral())
      // return (ST->getName().str().find("union.") != std::string::npos) ||
      //        (ST->getName().str().find("std::") != std::string::npos);
      // NOTE: the above introduces FPs in some benchmarks while fixing others
      return (ST->getName().str().find("class.std::") != std::string::npos ||
              ST->getName().str().find("struct.std::") != std::string::npos);
    // NOTE: assuming std types are safe just because are in the std lib is bad.
    // They are (mis)used all over SPEC benchmarks.
  }
  return false;
}

bool shouldSkipAlloca(Type *t) {
  if (t->isStructTy()) {

    StructType *ST = dyn_cast<StructType>(t);
    if (!ST->isLiteral())
      // return (ST->getName().str().find("union.") != std::string::npos) ||
      //        (ST->getName().str().find("std::") != std::string::npos) ||
      //        (ST->getName().str().find("int2type") != std::string::npos) ||
      //        (ST->getName().str().find("std::_List_iterator") !=
      //         std::string::npos);
      return (ST->getName().str().find("union.") != std::string::npos) ||
             (ST->getName().str().find("std::") != std::string::npos);
  }
  return false;
}
// __attribute__((noinline))
bool HWAddressSanitizer::instrumentStack(memtag::StackInfo &SInfo,
                                         const DominatorTree &DT,
                                         const PostDominatorTree &PDT,
                                         const LoopInfo &LI,
                                         const DataLayout &DL) {
  unsigned int I = 0;

  for (auto &KV : SInfo.AllocasToInstrument) {
    auto N = I++;
    auto *AI = KV.first;
    memtag::AllocaInfo &Info = KV.second;
    Value *Tag = nullptr;

    if (AllocaInst *AIcast = dyn_cast<AllocaInst>(AI)) {
      Type *allocatedType = AIcast->getAllocatedType();

      if (allocatedType->isArrayTy()) {
        auto elementType = allocatedType->getArrayElementType();
        if (elementType->isStructTy()) {
          StructType *ST_internal = dyn_cast<StructType>(elementType);
          if (ST_internal->isLiteral())
            continue;
          else if (ST_internal->getName().str().find("union.") == 0) {
            continue;
          }
        } // case: 1d array of structs

        else if (elementType->isArrayTy()) {
          // multi-dimensional array
          auto innerElementType = elementType->getArrayElementType();
          if (innerElementType->isStructTy()) {
            StructType *ST_internal_l2 = dyn_cast<StructType>(innerElementType);
            if (ST_internal_l2->isLiteral())
              continue;
            else if (ST_internal_l2->getName().str().find("union.") == 0) {
              continue;
            }
          } // case: 2d array of structs

          else {
            continue;
          } // case: 2d array of scalars or other types I don't care about atm

        } // case 2d array

        else {
          continue;
        } // case : array of scalars/NA
      } // case : alloca of ARRAY

      if (!allocatedType->isStructTy()) {
        continue;
      } else {
        StructType *ST = dyn_cast<StructType>(allocatedType);
        if (ST->isLiteral())
          continue;
        else if (ST->getName().str().find("union.") == 0) {
          continue;
        }
      } // rules out allocas of not safe structs
    } // cast AI
    else
      assert(false && "Allocas must be AllocaInsts");

    // AT THIS POINT, IT'S EITHER A STRUCT, A 1d ARRAY OF STRUCTS, OR A 2d ARRAY
    // OF STRUCTS
    IRBuilder<> IRB(AI->getNextNonDebugInstruction());
    if (!Tag)
      Tag = getRPTag(IRB);
    Value *AILong = IRB.CreatePointerCast(AI, IntptrTy);
    Value *AINoTagLong = untagPointer(IRB, AILong);
    Value *Replacement = tagPointer(IRB, AI->getType(), AINoTagLong, Tag);
    std::string Name =
        AI->hasName() ? AI->getName().str() : "alloca." + itostr(N);
    Replacement->setName(Name + ".fieldarmor");
    size_t Size = memtag::getAllocaSizeInBytes(*AI);
    Value *AICast = IRB.CreatePointerCast(AI, PtrTy);

    auto HandleLifetime = [&](IntrinsicInst *II) {
      II->setArgOperand(0, ConstantInt::get(Int64Ty, Size));
      II->setArgOperand(1, AICast);
    };

    llvm::for_each(Info.LifetimeStart, HandleLifetime);
    llvm::for_each(Info.LifetimeEnd, HandleLifetime);

    tagAlloca(IRB, AI, DL); // insert a call to fieldarmor_tag_memory function

    AI->replaceUsesWithIf(Replacement, [AICast, AILong](const Use &U) {
      auto *User = U.getUser();
      return User != AILong && User != AICast && !isa<LifetimeIntrinsic>(User);
    });

    auto TagEnd = [&](Instruction *Node) {
      IRB.SetInsertPoint(Node);
      untagAlloca(IRB, AI, DL);
    };

    for (auto *RI : SInfo.RetVec)
      TagEnd(RI);

    for (auto &II : Info.LifetimeStart)
      II->eraseFromParent();
    for (auto &II : Info.LifetimeEnd)
      II->eraseFromParent();
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

bool HWAddressSanitizer::selectiveInstrumentationShouldSkip(
    Function &F, FunctionAnalysisManager &FAM) const {
  auto SkipHot = [&]() {
    if (!ClHotPercentileCutoff.getNumOccurrences())
      return false;
    auto &MAMProxy = FAM.getResult<ModuleAnalysisManagerFunctionProxy>(F);
    ProfileSummaryInfo *PSI =
        MAMProxy.getCachedResult<ProfileSummaryAnalysis>(*F.getParent());
    if (!PSI || !PSI->hasProfileSummary()) {
      ++NumNoProfileSummaryFuncs;
      return false;
    }
    return PSI->isFunctionHotInCallGraphNthPercentile(
        ClHotPercentileCutoff, &F, FAM.getResult<BlockFrequencyAnalysis>(F));
  };

  bool Skip = SkipHot();
  emitRemark(F, FAM.getResult<OptimizationRemarkEmitterAnalysis>(F), Skip);
  return Skip;
}

/** Blocklist C++ templates because they are broken with my instumentation.*/
bool HWAddressSanitizer::potentiallyBlacklistFunction(Function &F) {
  // std::string demangledName = demangle(F.getName().str());

  // // blocking functions that start with std:: (enforce starts with)
  // if ((demangledName.find("std::") != std::string::npos &&
  //      demangledName.find("std::") == 0) ||
  //     demangledName.find("llvm::") != std::string::npos) {
  //   // errs() << "[++] Blocklisting function: " << demangledName << "\n";
  //   return true;
  // }

  // if (demangledName.find("Perl_Slab") != std::string::npos) {
  //   errs() << "[++] Blocklisting function: " << demangledName << "\n";
  //   return true;
  //   // TODO: solve bugs in there because of PTR arithmetics.
  //   // PtrToInt instrumentation was solving the mess there, so it must be
  //   easy
  //   // to figure bugs out. Only two functions are blocklisted.
  // }
  return false;
}

// TODO: handle extractvalue
void HWAddressSanitizer::sanitizeFunction(Function &F,
                                          FunctionAnalysisManager &FAM) {
  if (&F == HwasanCtorFunction)
    return;

  // Do not apply any instrumentation for naked functions.
  if (F.hasFnAttribute(Attribute::Naked))
    return;

  if (!F.hasFnAttribute(Attribute::SanitizeHWAddress)) {
    // errs( ) << "[HWASan] Skipping function without sanitize-hwaddress
    // attribute: "
    //        << F.getName() << "\n";
    return;
  }

  if (F.empty())
    return;
  // if (potentiallyBlacklistFunction(F))
  //   return;
  NumTotalFuncs++;
  // errs() << "[FSan] Instrumenting function: " << F.getName() << "\n";
  OptimizationRemarkEmitter &ORE =
      FAM.getResult<OptimizationRemarkEmitterAnalysis>(F);

  // if (selectiveInstrumentationShouldSkip(F, FAM))
  //   return;
  // NOTE: this was removed to instrument as much as possible.
  NumInstrumentedFuncs++;
  // errs() << "Instrumenting function: " << F.getName() <<
  // "-------------------\n";
  SmallVector<InterestingMemoryOperand, 16> OperandsToInstrument;
  SmallVector<MemIntrinsic *, 16> IntrinToInstrument;
  SmallVector<Instruction *, 8> LandingPadVec;

  // FieldArmor
  SmallVector<GetElementPtrInst *, 40> GEPsToInstrument;
  SmallVector<CmpInst *, 40> CMPsToInstrument;
  SmallVector<ConstantExpr *, 40> ConstGEPsToInstrument;
  SmallVector<StoreInst *, 40> StoresToInstrument;
  SmallVector<std::pair<CallInst *, std::string>, 40> CallsToAllocator;
  SmallVector<std::pair<CallInst *, std::string>, 40> CallsToNew;
  // FieldArmor

  const TargetLibraryInfo &TLI = FAM.getResult<TargetLibraryAnalysis>(F);

  memtag::StackInfoBuilder SIB(SSI, DEBUG_TYPE);
  for (auto &Inst : instructions(F)) {

    if (InstrumentStack) {
      SIB.visit(ORE, Inst);
    }

    if (InstrumentLandingPads && isa<LandingPadInst>(Inst))
      LandingPadVec.push_back(&Inst);

    // TODO: filter out something
    // TODO: I am ignoring ORE at the moment, I think it's fine to have the
    // RemarkEmitter emit info in SIB, just double check that it does not break
    // stuff.
    getInterestingMemoryOperands(ORE, &Inst, TLI, OperandsToInstrument);

    /* NOTE: ideally, one wants to instrument memcpy/memmove/memset only when
     * they operate on non-root pointers*/
    if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(&Inst))
      // if (!ignoreMemIntrinsic(ORE, MI))
      IntrinToInstrument.push_back(MI);

    if (GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(&Inst)) {
      GEPsToInstrument.push_back(GEPI);
    }

    if (CmpInst *CI = dyn_cast<CmpInst>(&Inst)) {
      CMPsToInstrument.push_back(CI);
    }
    // TODO: sub between ptrs has weird result
    // TODO: compiler can decide to statically fold some arithmetics to wrong
    // result -> InstCombiner does this, replacing the wrong value

    if (CallInst *CI = dyn_cast<CallInst>(&Inst)) {
      Function *Callee = CI->getCalledFunction();
      if (!Callee)
        continue;
      std::string demangledName = demangle(Callee->getName().str());
      if (demangledName == "malloc" || demangledName == "realloc" ||
          demangledName == "calloc" || demangledName == "reallocarray" ||
          demangledName == "memalign" || demangledName == "aligned_alloc" ||
          demangledName == "posix_memalign" || demangledName == "valloc" ||
          demangledName == "pvalloc") {
        CallsToAllocator.push_back(std::make_pair(CI, demangledName));
      }

      else if (demangledName.find("operator new") != std::string::npos) {
        CallsToAllocator.push_back(std::make_pair(CI, demangledName));
      }
    }
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(&Inst)) {
      if (CE->getOpcode() == Instruction::GetElementPtr) {
        ConstGEPsToInstrument.push_back(CE);
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
      IntrinToInstrument.empty())
    return;

  assert(!ShadowBase);

  BasicBlock::iterator InsertPt = F.getEntryBlock().begin();
  IRBuilder<> EntryIRB(&F.getEntryBlock(), InsertPt);
  // emitPrologue(EntryIRB,
  //              /*WithFrameRecord*/ ClRecordStackHistory != none &&
  //                  Mapping.withFrameRecord() &&
  //                  !SInfo.AllocasToInstrument.empty());

  for (auto &PAIR : CallsToAllocator) {
    TagAllocChunksBeforeUse(PAIR.first, PAIR.second);
  }

  // for (auto &PAIR : CallsToNew) {
  //   // HandleNewOperator(PAIR.first, PAIR.second);
  //   TagAllocChunksBeforeUse(PAIR.first, PAIR.second);
  // }

  if (!SInfo.AllocasToInstrument.empty()) {
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

  if (ClInstrumentMemIntrinsics && !IntrinToInstrument.empty()) {
    for (auto *Inst : IntrinToInstrument)
      instrumentMemIntrinsic(Inst);
  }

  for (auto &GEPI : GEPsToInstrument) {
    InstrumentGEP(GEPI);
  }

  /** NOTE: in this LLVM version, at O2, ConstGEPs do not seem to be there in
   * SPEC2017.
   * TODO: investigate */
  for (auto &CE : ConstGEPsToInstrument) {
    InstrumentConstGEP(CE);
  }

  // NOTE: cmps are instrumented because the same pointer can have different
  // tags depending on how it is retrieved.
  for (auto &CMPI : CMPsToInstrument) {
    InstrumentCMP(CMPI);
  }

  // TODO: properly handle container-of macros
  // NOTE: container_of-like macros subtract ints to pointers. To preserve
  // semantic, tag is removed so that the result is always untagged. This causes
  // tag loss. However, FPs resulting from a non-root ptr used to access a
  // struct are ruled out by default.
  // NOTE: enabling this breaks 502 -> TODO: investigate more. It seems to be
  // necessary for 520.

  /* NOTE: at O2, most arithmetic operations seem to be taken care by the
   * compiler. It folds constants in such a way that nothing is performed at
   * runtime and that code is safe. E.g. compiling 500.perlbench_r at O0 causes
   * an invalid malloc when size is computed using ptr arithm. */
  // for (auto &BO : ArithInstructions) {
  //   InstrumentArithmetic(BO);
  // }

  // TODO: remove checks on ".untagged" pointers.
  DominatorTree *DT = FAM.getCachedResult<DominatorTreeAnalysis>(F);
  PostDominatorTree *PDT = FAM.getCachedResult<PostDominatorTreeAnalysis>(F);
  LoopInfo *LI = FAM.getCachedResult<LoopAnalysis>(F);
  DomTreeUpdater DTU(DT, PDT, DomTreeUpdater::UpdateStrategy::Lazy);
  const DataLayout &DL = F.getDataLayout();
  for (auto &Operand : OperandsToInstrument)
    instrumentMemAccess(Operand, DTU, LI, DL);
  DTU.flush();
  /** NOTE: keeping the DomTree up-to-date might be necessary even for the above
   * transformations. TODO: implement and test.*/

  ShadowBase = nullptr;
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

Value *HWAddressSanitizer::GetArraySize(CallInst *CI, StructType *t,
                                        IRBuilder<> &IRB) {
  std::string demangledName =
      CI->getCalledFunction()
          ? demangle(CI->getCalledFunction()->getName().str())
          : "";
  if (demangledName == "") {
    errs()
        << "[FieldArmor] WARNING: could not demangle function name for call: "
        << *CI << "\n";
    return 0;
  }

  uint64_t typeSize = M.getDataLayout().getTypeAllocSize(t);

  if (typeSize == 0) {
    errs() << "[FieldArmor] WARNING: could not get type size for struct: ";
    t->print(errs());
    errs() << "SIZED?" << t->isSized() << "\n";
    return nullptr;
  }

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

  errs() << "[FieldArmor] WARNING: allocator not handled for size "
            "reconstruction: "
         << demangledName << "\n";
  return nullptr;
}

Type *fromString(std::string S, LLVMContext &C) {
  // TODO: complete for classes
  if (S == "i1")
    return Type::getInt1Ty(C);
  if (S == "i8" || S == "i8*")
    return Type::getInt8Ty(C);
  if (S == "i16" || S == "i16*")
    return Type::getInt16Ty(C);
  if (S == "i32" || S == "i32*")
    return Type::getInt32Ty(C);
  if (S == "i64" || S == "i64*")
    return Type::getInt64Ty(C);
  if (S == "float" || S == "float*")
    return Type::getFloatTy(C);
  if (S == "double" || S == "double*")
    return Type::getDoubleTy(C);
  if (S == "void" || S == "void*")
    return Type::getVoidTy(C);
  if (S.find("**") != std::string::npos || S == "struct.") {
    // just for convenience
    // struct. is a literal struct -> TODO: handle later ...
    return Type::getVoidTy(C);
  }
  if (S.find("class.") != std::string::npos ||
      S.find("union.") != std::string::npos)
    // TODO: refine
    return Type::getVoidTy(C);
  return nullptr;
}

// returns if TS is ambiguous
bool augmentstructTypesFromTypeSet(std::set<Type *> &structTypes,
                                   const TypeSet *ts, LLVMContext &C,
                                   std::set<Type *> &seenTypes) {
  auto before = structTypes.size();
  int count = 0;
  for (auto &t : ts->types)
    if (t.find("class.") != std::string::npos ||
        t.find("struct.") != std::string::npos)
      count++;
  if (count > 1) {
    errs() << "\t\t [FieldArmor] WARNING amb: TypeSet contains multiple "
              "struct/class types.\n";
    for (auto &t : ts->types) {
      errs() << "\t\t\t TypeSet type: " << t << "\n";
    }
    return true;
  }
  for (auto &t : ts->types) {
    int levelsOfInd = std::count(t.begin(), t.end(), '*');

    if (levelsOfInd > 2) {
      errs() << "\t\t [FieldArmor] WARNING: skipping array of pointers: " << t
             << "\n";
      Type *tmp = fromString(t, C);
      if (tmp)
        seenTypes.insert(tmp);
      return false;
    }
    bool containsPorcodio = (t.find('%') != std::string::npos);
    auto subStringSize = t.find_first_of('*') -
                         (containsPorcodio ? t.find_first_of('%') + 1 : 0);
    // note: this could contain the name "union"
    std::string substringWithNoAsterisk = t.substr(
        containsPorcodio ? t.find_first_of('%') + 1 : 0, subStringSize);

    StructType *ST = StructType::getTypeByName(C, substringWithNoAsterisk);
    if (!ST) {
      // try again, maybe it's a union and TypeCopilot puts spaces
      std::string maybeUnionName = substringWithNoAsterisk;
      std::replace(maybeUnionName.begin(), maybeUnionName.end(), ' ', '.');
      ST = StructType::getTypeByName(C, maybeUnionName);
      if (ST) {
        errs() << "\t\t Retrieved StructType from name: " << t
               << " levels of indirection: " << levelsOfInd << "\n";
        ST->print(errs());
        errs() << "\n";
        structTypes.insert(ST);
        seenTypes.insert(ST);
        continue;
      } else {
        errs() << "\t\t [FieldArmor] WARNING: could not get StructType "
                  "from name: "
               << substringWithNoAsterisk << "\n";
      }

      // classes names only make sense inside a namespace
      // TODO: handle this
      Type *tmp = fromString(substringWithNoAsterisk, C);
      if (tmp)
        seenTypes.insert(tmp);
      continue;
    } else
      errs() << "\t\t Retrieved StructType from name: " << t
             << " levels of indirection: " << levelsOfInd << "\n";
    ST->print(errs());
    errs() << "\n";
    structTypes.insert(ST);
    seenTypes.insert(ST);
  }
  // bool changed = (structTypes.size() - before) > 0;
  // if (changed)
  //   errs() << "\t\t [FieldArmor] INTERESTING INFO: populated structTypes from
  //   "
  //             "TypeSet.\n";
  return false;
} // augmentstructTypesFromTypeSet

void debugCallSitePrint(CallInst *CI,
                        const std::string &demangledFunctionName) {
  errs() << "ALLOC SITE: ";
  CI->print(errs());
  errs() << "\n";

  errs() << " FUNCTION: " << demangledFunctionName << "\n";
  if (const DebugLoc &DL = CI->getDebugLoc()) {
    if (DILocation *Loc = DL.get()) {
      StringRef File = Loc->getFilename();
      StringRef Dir = Loc->getDirectory();
      unsigned Line = Loc->getLine();
      unsigned Col = Loc->getColumn();
      errs() << "    LOCATION: " << Dir << "/" << File << ":" << Line << ":"
             << Col << "\n";
    }
  } else
    errs() << "\tLOCATION: <unknown>\n";
}

Value *retrieveTagVector(StructType *srcType, Module &M, bool try_base = true) {
  auto typeName = srcType->getStructName().str();
  // bool isClass = typeName.find("class.") == 0;
  bool isBase = typeName.find(".base") != std::string::npos;
  // isClass &&

  std::string lookupName = typeName;
  if (!isBase && try_base)
    lookupName = typeName + ".base";

  auto tagVector = M.getGlobalVariable(lookupName + ".fieldarmor.tagvec", true);
  if (!tagVector) {
    errs() << "[FieldArmor] LOOKUP ERROR: Tag vector for struct type: ";
    srcType->print(errs());
    errs() << "lookup type: " << lookupName;
    errs() << "\n";
    return nullptr;
  }

  errs() << "[FieldArmor] LOOKUP OK: Retrieved tag vector for LOOKUP NAME: "
         << lookupName << ", type name: " << typeName << "\n";
  return tagVector;
}

Type *
HWAddressSanitizer::figureOutInheritance(const std::set<Type *> &structTypes) {
  // compute BASE types set
  std::set<StructType *> baseTypes;
  for (auto *t : structTypes) {

    if (auto *ST = dyn_cast<StructType>(t)) {
      if (ST->isOpaque() || ST->isLiteral()) {
        errs() << "[FieldArmor] WARNING: skipping opaque or literal type: ";
        return nullptr;
      }
      auto name = ST->getStructName().str();
      if (name.find(".base") != std::string::npos) {
        baseTypes.insert(ST);
      } else {
        auto *baseType = StructType::getTypeByName(*C, name + ".base");
        if (baseType) {
          baseTypes.insert(baseType);
        } else {
          // no base type, put it as is
          baseTypes.insert(ST);
        }
      }
    } else {
      // not a struct, put it as is
      errs()
          << "[FieldArmor] WARNING: type is not a struct, skipping inheritance "
             "analysis for type: ";
      t->print(errs());
      errs() << "\n";
    }
  }

  struct TypeWithSize {
    uint64_t Size;
    Type *Ty;
  };

  struct LargerSizeFirst {
    bool operator()(const TypeWithSize &a, const TypeWithSize &b) const {
      return a.Size < b.Size; // max-heap
    }
  };

  std::priority_queue<TypeWithSize, std::vector<TypeWithSize>, LargerSizeFirst>
      typesWithSize;

  auto &DL = M.getDataLayout();

  for (auto *t : baseTypes) {
    typesWithSize.push({DL.getTypeAllocSize(t), t});
  }
  if (typesWithSize.empty()) {
    errs() << "[FieldArmor] WARNING: no struct types found in structTypes set, "
              "cannot figure out inheritance.\n";
    return nullptr;
  }
  errs() << "[FieldArmor] INFO: sorted struct types by size, biggest first:\n";
  auto ret = typesWithSize.top().Ty;
  for (; !typesWithSize.empty(); typesWithSize.pop())
    errs() << "\tType: " << typesWithSize.top().Ty->getStructName()
           << ", Size: " << typesWithSize.top().Size << "\n";
  return ret;
}

// TODO: patch Frontend to make sure Structs emerge even when they are only used
// as i8

// TODO: handle xmalloc and xcalloc, these wrappers are simple
// TODO: handle ConstExpr GEPs used as pointers in the StoreInsts
// TODO: convert TypeSet members to IR types
// TODO: debug arrays of pointers, everything is wrong here!!!
// TODO: correctly identify structs in C++ classes
// TODO: rule out partial tagging of aggregates

/** Is it an allocator? Is it an explicit array alloc? */
std::pair<bool, bool> getAllocationMetadata(Function *F) {
  auto name = F->getName();
  auto demangledName = demangle(name);
  bool isArray = false;
  if (demangledName == "malloc" || demangledName == "realloc" ||
      demangledName == "calloc" || demangledName == "reallocarray" ||
      demangledName == "memalign" || demangledName == "aligned_alloc" ||
      demangledName == "posix_memalign" || demangledName == "valloc" ||
      demangledName == "pvalloc" ||
      demangledName.find("operator new") != std::string::npos) {
    isArray = (demangledName == "calloc" || demangledName == "reallocarray" ||
               demangledName.find("operator new[]") != std::string::npos);
    return {true, isArray};
  }
  return {false, false};
} // getAllocationMetadata

/** Analyze uses at allocation site, if a type can be reliably reconstructed,
 * then tag memory. This almost never works.*/
void HWAddressSanitizer::TagAllocChunksBeforeUse(
    CallInst *CI, const std::string &DemangledName) {
  std::set<Type *> seenTypes;
  std::set<Type *> structTypes;
  Type *finalType = nullptr;
  bool ambiguous = false;
  auto nUses = CI->getNumUses();
  debugCallSitePrint(CI, DemangledName);

  // NOTE: this is weird, but it happens in some benchmarks. These calls will
  // probably be dropped.
  if (nUses == 0)
    return;

  for (auto *U : CI->users()) {
    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(U)) {
      if (GEP->getOperand(0) != CI)
        continue;
      Type *tmp = GEP->getSourceElementType();
      std::string typeName;
      raw_string_ostream rso(typeName);
      tmp->print(rso);
      if (typeName == "ptr") {
        // TODO: can I reuse this info for further type propagation in the
        // TypeInferenceAnalysis?
        errs() << "\t\t [FieldArmor] Skipping GEP on array of ptrs" << *GEP
               << "\n";
        return;
      }

      if (tmp->isStructTy())
        structTypes.insert(tmp);
      seenTypes.insert(tmp);
    } // GEP USER

    else if (StoreInst *SI = dyn_cast<StoreInst>(U)) {
      auto valueOperand = SI->getValueOperand();

      if (valueOperand != CI)
        continue; // TODO

      auto ptrOperand = SI->getPointerOperand();
      // TODO: does getUnderlyingObject retrieve the object underlying a GEP on
      // a struct field?
      auto underlyingObject = getUnderlyingObject(ptrOperand);

      if (ConstantExpr *CR = dyn_cast<ConstantExpr>(ptrOperand)) {
        // Storing the ptr inside a field of a GV struct

        if (CR->getOpcode() == Instruction::GetElementPtr) {
          // TODO: extend this case to handle arrays!
          GlobalVariable *GV = dyn_cast<GlobalVariable>(underlyingObject);
          if (!GV || !GV->getValueType()->isStructTy())
            continue;

          errs() << "\t\t STORE IN CONSTEXPR GEP: " << *CR << "\n";
          errs() << "\t\t Underlying object of CE GEP: ";
          underlyingObject->print(errs());

          auto *GEP = dyn_cast<GEPOperator>(CR);
          auto *offset = GEP->getOperand(1);
          auto *ConstOffset = dyn_cast<ConstantInt>(offset);
          uint64_t IntOffset = ConstOffset->getZExtValue();

          const DataLayout &DL = M.getDataLayout();
          StructType *StructTy = dyn_cast<StructType>(GV->getValueType());
          const StructLayout *SL = DL.getStructLayout(StructTy);
          unsigned FieldIdx = SL->getElementContainingOffset(IntOffset);
          errs() << "\n\t\t GEP field index: " << FieldIdx << "\n";
          std::string field =
              RetrievedTypes->helper->getDIStructField(StructTy, FieldIdx);
          bool containsPorcodio = false;

          if (field == "") {
            errs()
                << "\t\t [FieldArmor] WARNING: could not get field name from "
                   "debug info for struct: ";
            StructTy->print(errs());
            errs() << " field index: " << FieldIdx << "\n";
            continue;
          } else {
            containsPorcodio = (field.find("%") != std::string::npos);
          }

          auto subStringSize =
              field.find_first_of('*') -
              (containsPorcodio ? field.find_first_of('%') + 1 : 0);
          std::string clean_name =
              field.substr(containsPorcodio ? field.find_first_of('%') + 1 : 0,
                           subStringSize);

          StructType *FieldType = StructType::getTypeByName(*C, clean_name);
          if (FieldType) {
            structTypes.insert(FieldType);
            errs() << "\t\t Retrieved StructType from field name: " << field
                   << "\n";
            FieldType->print(errs());
            errs() << "\n";
          } else
            errs() << "\t\t [FieldArmor] WARNING: could not get StructType "
                      "from field name:"
                   << clean_name << "\n";

          // STATISTICS
          Type *tmp = fromString(clean_name, *C);
          if (tmp)
            seenTypes.insert(tmp);
          // STATISTICS
        } // STORE in CONSTEXPR GEP
        else {
          errs() << "\t\t [FieldArmor] WARNING: STORE in UNKNOWN CONSTEXPR "
                 << *CR << "\n";
        }
      } // STORE in FIELD of GLOBAL via CONSTEXPR GEP

      else if (GlobalVariable *GV =
                   dyn_cast<GlobalVariable>(underlyingObject)) {
        // storing in a global pointer
        errs() << "\t\t STORE IN GLOBAL: " << *GV << "\n";

        // auto F = SI->getFunction();
        const TypeSet *ts = RetrievedTypes->lookup(GV, nullptr);

        if (ts)
          ambiguous =
              augmentstructTypesFromTypeSet(structTypes, ts, *C, seenTypes);
        else
          errs() << "\t\t <none> - TypeCopilot FAIL on GLOBAL VAR TYPE\n";
      } // STORE in GLOBAL

      else if (GetElementPtrInst *GEP_ptrOperand =
                   dyn_cast<GetElementPtrInst>(ptrOperand)) {
        errs() << "\t\t STORE IN STRUCT FIELD   " << *GEP_ptrOperand << "\n";
        // TODO: extend this case to handle arrays!
        bool isTwoOpGEP = GEP_ptrOperand->getNumOperands() ==
                          2; // access to an array of something
        if (isTwoOpGEP) {
          std::string op_name = GEP_ptrOperand->getOperand(0)->getName().str();
          errs() << "\t\t Two-op GEP detected, name: " << op_name << "\n";
          if (!op_name.empty() &&
              op_name.find("invariant.") != std::string::npos) {
            // 100% mistaken if you use this
            errs() << "\t\t [FieldArmor] WARNING: skipping invariant GEP: "
                   << *GEP_ptrOperand << "\n";
            continue;
          }
          auto *GEPType = GEP_ptrOperand->getSourceElementType();
          seenTypes.insert(
              GEPType); // this might insert i8 on GEP structs? TODO
          if (GEPType->isStructTy()) {
            structTypes.insert(GEPType);
            errs() << "\t\t Retrieved StructType from 2-op GEP: ";
            GEPType->print(errs());
            errs() << "\n";
            continue;
          }
        }
        const TypeSet *ts =
            RetrievedTypes->lookup(GEP_ptrOperand, SI->getFunction());
        if (ts)
          ambiguous =
              augmentstructTypesFromTypeSet(structTypes, ts, *C, seenTypes);
        else
          errs() << "\t\t ts = <none> - TypeCopilot FAIL on STRUCT FIELD\n";

      } // STORE in GEP

      else if (AllocaInst *AI = dyn_cast<AllocaInst>(underlyingObject)) {
        errs() << "\t\t STORE IN ALLOCA: " << *AI << "\n";
        const TypeSet *ts = RetrievedTypes->lookup(AI, SI->getFunction());
        if (ts)
          ambiguous =
              augmentstructTypesFromTypeSet(structTypes, ts, *C, seenTypes);
        else
          errs() << "\t\t ts = <none> - TypeCopilot FAIL on ALLOCA\n";
        auto *type = AI->getAllocatedType();
        if (type->isStructTy()) {
          structTypes.insert(type);
          errs() << "\t\t Retrieved StructType from alloca: ";
          type->print(errs());
          errs() << "\n";
        }
        seenTypes.insert(type);
        continue;
      } // STORE in ALLOCA

      else if (PHINode *PN = dyn_cast<PHINode>(underlyingObject)) {
        errs() << "\t\t STORE IN PHI NODE: TODO " << *PN << "\n";
        // processPHI(PN, seenTypes, structTypes); // TODO
        continue;
      } // STORE in PHI
      else {
        // TODO:
        errs() << "\t\t [FieldArmor] WARNING: STORE in UNKNOWN ptr TODO: ";
        ptrOperand->print(errs());
        errs() << "\n";
        auto underlyingObject = getUnderlyingObject(ptrOperand);
        errs() << "\t\t Underlying object: ";
        underlyingObject->print(errs());
        errs() << "\n";
        // could be a function argument or something derived from it
      } // STORE in UNKNOWN ptr
    } // STORE USER

    else if (CallInst *CII = dyn_cast<CallInst>(U)) {
      Type *typeOfArg = nullptr;
      Function *Callee = CII->getCalledFunction();

      if (!Callee) {
        // NOTE: I think we can't do anything in this case
        errs() << "\t\t CALL USER INDIRECT CALL: ";
        CII->print(errs());
        errs() << "\n";
        continue;
      }

      if (Callee->getName().find("llvm.memcpy") != std::string::npos ||
          Callee->getName().find("llvm.memmove") != std::string::npos ||
          Callee->getName().find("llvm.memset") != std::string::npos ||
          Callee->getName().find("memcpy") != std::string::npos ||
          Callee->getName().find("memmove") != std::string::npos ||
          Callee->getName().find("memset") != std::string::npos ||
          Callee->getName().find("free") != std::string::npos ||
          Callee->getName().find("printf") != std::string::npos) {
        // these functions dont tell me anything
        // skip memcpy/memmove calls
        errs() << "\t\t CALL USER (memcpy/memmove/memset/free/printf): ";
        CII->print(errs());
        errs() << "\n";
        continue;
      }

      std::string calleeName = demangle(Callee->getName().str());
      if (calleeName == "strlen" || calleeName == "strcpy" ||
          calleeName == "strcmp" || calleeName == "strcat") {
        errs()
            << "[FieldArmor]\tTYPE RECON: UNINTERESTING: called function is ";
        errs() << calleeName << "\n";
        return; // ignore this allocation site
      }

      if (calleeName.find("operator delete") != std::string::npos) {
        errs() << "\t\t CALL USER (operator delete): ";
        CII->print(errs());
        errs() << ", IGNORING \n";
        continue;
      }

      errs() << "\t CALL USER: ";
      CII->print(errs());
      errs() << "\n";

      int idx = -1;
      for (unsigned i = 0; i < Callee->arg_size(); i++)
        if (CII->getArgOperand(i) == CI)
          idx = i;
      assert(idx != -1 && "malloc/realloc/calloc/new return value should be an "
                          "argument of the call user");

      const TypeSet *ts = RetrievedTypes->lookup(Callee->getArg(idx), Callee);

      if (ts) {
        errs() << "\t\t TypeSet from CALL ARG TYPE: ";
        for (auto &t : ts->types) {
          errs() << t << " ";
        }
        errs() << "\n";
        ambiguous =
            augmentstructTypesFromTypeSet(structTypes, ts, *C, seenTypes);
      }

      else {
        errs() << "\t\t ts = <none> - TypeCopilot FAIL on CALL ARG TYPE\n";
        continue;
      }
    } // CALL USER

    else if (ReturnInst *RI = dyn_cast<ReturnInst>(U)) {
      errs() << "\t\t RET USER: " << *RI << "\n";
      auto *functionThatIsReturning = RI->getFunction();
      const TypeSet *ts =
          RetrievedTypes->lookup(functionThatIsReturning, nullptr);
      if (ts) {
        errs() << "\t\t TypeSet from RET TYPE: ";
        for (auto &t : ts->types) {
          errs() << t << " ";
        }
        errs() << "\n";
        ambiguous =
            augmentstructTypesFromTypeSet(structTypes, ts, *C, seenTypes);
      } else
        errs() << "\t\t ts = <none> - TypeCopilot FAIL on RET TYPE, function: "
               << *functionThatIsReturning << "\n";
      // continue;
    } // RET USER

    else if (PHINode *PN = dyn_cast<PHINode>(U)) {
      errs() << "\t\t PHI USER: " << *PN << "\n";
      const TypeSet *ts = RetrievedTypes->lookup(PN, PN->getFunction());
      if (ts) {
        errs() << "\t\t TypeSet from PHI TYPE: ";
        for (auto &t : ts->types) {
          errs() << t << " ";
        }
        errs() << "\n";
        ambiguous =
            augmentstructTypesFromTypeSet(structTypes, ts, *C, seenTypes);
        for (auto *user : PN->users()) {
          errs() << "\t\t USER of PHI NODE: ";
          user->print(errs());
          errs() << "\n";
        }
      } else
        errs() << "\t\t ts = <none> - TypeCopilot FAIL on PHI TYPE\n";
    } // PHI USER

    else {
      errs() << "\t\t OTHER USER: ";
      U->print(errs());
      errs() << "\n";
    } // OTHER USER
  } // for each user
  if (ambiguous) {
    errs() << "[FieldArmor] AMBIGUITY. Bailing.\n";
    finalType = figureOutInheritance(structTypes);
    return;
    // return;
  }

  if (structTypes.empty()) {
    if (!seenTypes.empty()) {
      errs()
          << "[FieldArmor]\tTYPE RECON: UNINTERESTING: struct typeset empty\n";
      for (auto *type : seenTypes) {
        errs() << "\t Type: ";
        type->print(errs());
        errs() << "\n";
      }
      // very uncertain about this
      errs() << "[FieldArmor]\tTYPE RECON: CONDITIONAL SUCCESS\n";
    } else
      errs() << "[FieldArmor]\tTYPE RECON: no types found at all. \n";
    return;
  }

  if (structTypes.size() > 1) {
    // TODO: handle each path separately
    // TODO: potentially handle inheritance
    ambiguous = true;
    // errs() << "[FieldArmor]\tAMBIGUITY. Types: \n";
    for (auto *type : structTypes) {
      errs() << "\t Type: ";
      type->print(errs());
      errs() << "\n";
    }
    finalType = figureOutInheritance(structTypes);
  } // AMBIGUITY

  Type *type = nullptr;
  if (ambiguous) {
    errs() << "[FieldArmor] AMBIGUITY: multiple candidate struct types. "
              "Bailing.\n";
    return;
  }

  else
    type = *structTypes.begin();

  assert(type->isStructTy() &&
         "only struct types should remain in structTypes");

  // this does not imply tagging success, yet!
  errs() << "[FieldArmor]\tTYPE RECON SUCCESS! Inferred type: \n\t\t";
  type->print(errs());
  errs() << "\n";

  auto srcType = dyn_cast<StructType>(type);

  if (srcType->isLiteral() || srcType->getName().str().find("union.") == 0) {
    errs() << "[FieldArmor]\t\tTYPE NOT SUPPORTED: " << *srcType << "\n";
    return;
  }
  std::string typeName = srcType->getStructName().str();
  bool isBase = typeName.find(".base") != std::string::npos;
  Value *tagVector = nullptr;
  if (isBase) {
    tagVector = retrieveTagVector(srcType, M, true);
    if (!tagVector) {
      createTagVector(srcType);
      tagVector = retrieveTagVector(srcType, M, true);
      if (!tagVector) {
        errs() << "[FieldArmor] ERROR: could not CREATE & RETRIEVE tag vector "
                  "for BASE type: ";
        srcType->print(errs());
        errs() << "\n";
        return;
      }
    }
  } // isBase
  else {
    // does the base type exist?
    std::string baseTypeName = srcType->getStructName().str() + ".base";
    auto *baseType = StructType::getTypeByName(*C, baseTypeName);
    if (baseType) {
      tagVector = retrieveTagVector(srcType, M, true);
      if (!tagVector) {
        createTagVector(srcType);
        tagVector = retrieveTagVector(srcType, M, true);
        if (!tagVector) {
          errs() << "[FieldArmor] ERROR: could not CREATE & RETRIEVE tag "
                    "vector for BASE type: ";
          srcType->print(errs());
          errs() << "\n";
          return;
        }
      }
    } else {
      tagVector = retrieveTagVector(srcType, M, false);
      if (!tagVector) {
        createTagVector(srcType);
        tagVector = retrieveTagVector(srcType, M, false);
        if (!tagVector) {
          errs() << "[FieldArmor] ERROR: could not CREATE & RETRIEVE tag "
                    "vector for type: ";
          srcType->print(errs());
          errs() << "\n";
          return;
        }
      }
    }
  } // NOT base

  // at this point, it can be a class or a struct
  IRBuilder<> IRB(CI->getNextNonDebugInstruction());
  // NOTE: this is safe even if before ICMP null because of how the runtime
  // tagging function is written

  FunctionCallee fieldarmor_tag_memory =
      M.getOrInsertFunction("_ZN8__hwasan21fieldarmor_tag_memoryEPvmm", PtrTy,
                            PtrTy, PtrTy, Int64Ty, Int64Ty);

  Value *ArraySizeValue = GetArraySize(CI, srcType, IRB);
  if (!ArraySizeValue) {
    errs() << "[FieldArmor] ERROR SIZE RECON FOR ALLOC CALL: ";
    CI->print(errs());
    errs() << "\tARG 0: ";
    CI->getArgOperand(0)->print(errs());
    errs() << "\n";
    return;
  }

  uint64_t typeSize = M.getDataLayout().getTypeAllocSize(srcType);
  // TODO: if typeSize is lt single element size, this is a partial type
  // reconstruction. But how do I know this statically?
  errs() << "[FieldArmor]\t\tDYNAMIC TAGGING SUCCESS: "
         << srcType->getStructName() << ", array size: " << *ArraySizeValue
         << "\n\n";

  IRB.CreateCall(fieldarmor_tag_memory,
                 {IRB.CreatePointerCast(CI, PtrTy),
                  IRB.CreatePointerCast(tagVector, PtrTy),
                  ConstantInt::get(Int64Ty, typeSize), ArraySizeValue});
  CI->setName(CI->getName() + ".fieldarmor.tagged");
  structTypes.clear();
} // TagAllocChunksBeforeUse

void HWAddressSanitizer::handleGEP2operands(GetElementPtrInst *GEPI) {
  // auto GEPResultType = GEPI->getResultElementType();
  // TODO: look into this. How's vector implemented?
  if (GEPI->getType()->isStructTy() && !GEPI->getType()->isVectorTy()) {
    errs() << "[HWASAN] Instrumenting 2-operands GEP into struct: ";
    GEPI->print(errs());
    errs() << "\n";
    GEPI->getType()->print(errs());
    errs() << "\n";
    IRBuilder<> IRB(GEPI->getNextNonDebugInstruction());
    Value *resultLong =
        IRB.CreatePointerCast(GEPI, IntptrTy); // this breaks for some GEPs

    Value *untaggedResLong = untagPointer(IRB, resultLong);
    Value *taggedPointer =
        tagPointer(IRB, GEPI->getType(), untaggedResLong,
                   ConstantInt::get(IntptrTy, RPTag)); // set RP bit
    std::string Name = GEPI->hasName() ? GEPI->getName().str()
                                       : "gep." + itostr(NumInstrumentedGEPs);
    taggedPointer->setName(Name + ".fieldarmor.struct");
    GEPI->replaceUsesWithIf(taggedPointer, [resultLong](const Use &U) {
      auto *User = U.getUser();
      return User != resultLong && !isa<LifetimeIntrinsic>(User);
    });
    NumInstrumentedGEPs++;
    return;
  }
}

void HWAddressSanitizer::InstrumentGEP(GetElementPtrInst *GEPI) {
  // NOTE: new corner case: pointer passed to a function and function stores
  // it

  // Q: can I tell GEPs on globals/stack apart from heap?
  // Q: what if some global pointer is stored in a stack variable and then
  // GEPed? Do I see a store?
  auto nOperands = GEPI->getNumOperands();
  // if(GEPI->hasName() && GEPI->getName().str().find("untagged") !=
  // std::string::npos){
  //   errs() << "[FSan] Skipping GEP on untagged pointer: ";
  //   GEPI->print(errs());
  //   errs() << "\n";
  //   return;
  // }
  // NOTE: this check never fails if un-squashing the GEPs in the frontend.
  assert(nOperands <= 3);
  if (nOperands != 3) {
    handleGEP2operands(GEPI);
    return;
  }

  auto fatherType = GEPI->getSourceElementType();
  auto sonType = GEPI->getResultElementType();
  auto gepName = GEPI->hasName() ? GEPI->getName().str()
                                 : "gep." + itostr(NumInstrumentedGEPs);

  IRBuilder<> IRB(GEPI->getNextNonDebugInstruction());
  Value *resultLong = IRB.CreatePointerCast(GEPI, IntptrTy);
  Value *untaggedResLong = untagPointer(IRB, resultLong);
  Value *untaggedResLongPtr =
      IRB.CreateIntToPtr(untaggedResLong, GEPI->getType());

  // Value *fullFatherTag = IRB.CreateLShr(
  //     IRB.CreateAnd(resultLong, ConstantInt::get(IntptrTy, 0x7FLu << 56Lu)),
  //     PointerTagShift);

  // Value *fatherT = IRB.CreateAnd(fullFatherTag, T_Mask_value);

  Value *fatherT = IRB.CreateLShr(
      IRB.CreateAnd(resultLong, ConstantInt::get(IntptrTy, 0x0FLu << 56Lu)),
      PointerTagShift);

  fatherT->setName("fatherT");
  std::string endResultName = "";
  Value *taggedPointer = nullptr;

  if (GEPI->hasName() &&
      GEPI->getName().str().find("invariant") != std::string::npos) {
    // NOTE: this removes some false positives for now.
    // TODO: find smarter solution to force GEPs to be there.
    taggedPointer = untaggedResLongPtr;
    endResultName = gepName + ".invariant.untagged";
  }

  else if (fatherType->isArrayTy()) {
    if (!sonType->isStructTy()) {
      // Preserve tag is GEP returns a) array, b) scalar.
      // NOTE: this assumes the pointer to the array is tagged.
      /* TODO: enforce this at allocation time using RPTag for everything or
       * do it here */
      return;
    } // GEP array -> <scalar, array>

    else { /** GEP into array of structs */
      // StructType *sonTypeCast = dyn_cast<StructType>(sonType);
      // GEP into non-literal struct array
      taggedPointer =
          tagPointer(IRB, GEPI->getType(), untaggedResLong,
                     ConstantInt::get(IntptrTy, RPTag)); // set RP bit
      endResultName = gepName + ".fieldarmor.struct";

    } // GEP into array of non-literal structs
  } // GEP from array type
  else if (fatherType->isVectorTy()) {
    if (!sonType->isStructTy()) {
      return;
    }
  }
  // FATHER IS STRUCT for sure now
  else if (fatherType->isStructTy()) {
    Value *sonTag = nullptr;
    auto sonIsScalar = !sonType->isStructTy();
    if (sonIsScalar) {
      auto sonIdx = IRB.CreateAnd(
          IRB.CreateAdd(IRB.CreateZExtOrTrunc(GEPI->getOperand(2), IntptrTy),
                        ConstantInt::get(IntptrTy, 0x1Lu)),
          ConstantInt::get(IntptrTy, T_Mask)); // modulo 16
      // NOTE: this add was a remnant of old fieldarmor scheme RLT
      // TODO:
      // Value *sonT = IRB.CreateAnd(IRB.CreateAdd(fatherT, sonIdx),
      //                             ConstantInt::get(IntptrTy, T_Mask));
      Value *sonT = IRB.CreateAnd(sonIdx, ConstantInt::get(IntptrTy, T_Mask));
      // NOTE: tags might be 0 after this operation. TODO: prevent it from
      // happening

      sonTag = sonT;
      // sonTag->setName("sonTag");
      taggedPointer = tagPointer(IRB, GEPI->getType(), untaggedResLong, sonTag);
      endResultName = gepName + ".fieldarmor.scalar";
    } // GEP struct -> scalar

    else { /** GEP struct -> struct */
      StructType *SonTy = dyn_cast<StructType>(sonType);
      if (SonTy->isOpaque()) {
        // Opaque structs are not tagged, they might be passed to the uninstr
        // lib
        taggedPointer = untaggedResLongPtr;
        NumUntaggedGEPResults++;
        endResultName =
            (GEPI->hasName() ? GEPI->getName().str()
                             : "gep." + itostr(NumInstrumentedGEPs)) +
            ".untagged";
      } else {
        sonTag = ConstantInt::get(IntptrTy, RPTag);
        endResultName = gepName + ".fieldarmor.struct";
        taggedPointer =
            tagPointer(IRB, GEPI->getType(), untaggedResLong, sonTag);
      }
    } // GEP struct -> struct
  } // FATHER IS STRUCT

  // assert(taggedPointer != nullptr && "taggedPointer cannot be null here");
  if (taggedPointer == nullptr) {
    // This should not happens
    errs() << "[HWASAN] Error: taggedPointer is null in GEP instrumentation!\n";
    GEPI->print(errs());
    GEPI->getSourceElementType()->print(errs());
    errs() << "\n";
    GEPI->getOperand(0)->print(errs());
    errs() << "\n";
    GEPI->getResultElementType()->print(errs());
    errs() << "\n";
    GEPI->getType()->print(errs());
    errs() << "\n";
    GEPI->getOperand(2)->print(errs());

    errs() << "\n";
    assert(taggedPointer != nullptr && "taggedPointer cannot be null here");
  }
  taggedPointer->setName(endResultName);
  GEPI->replaceUsesWithIf(taggedPointer, [resultLong, GEPI](const Use &U) {
    auto *User = U.getUser();
    bool safe = User != resultLong && !isa<LifetimeIntrinsic>(User);
    // NOTE: don't store tagged pointers that might be used by uninstrumented
    // code Q: can this fail with maps where something is stored with ptr key
    // and retrieved with tagged/untagged ptr? Q: how much detection power do
    // we lose, if any?
    // if (StoreInst *SI = dyn_cast<StoreInst>(User)) {
    //   if (SI->getValueOperand() == GEPI) {
    //     safe = false;
    //   }
    // }

    // TODO: this is too much, but how do we handle it?
    // else if (ReturnInst *RI = dyn_cast<ReturnInst>(User)) {
    //   if (RI->getReturnValue() == GEPI) {
    //     safe = false;
    //     // TODO: remove this crap
    //   }
    // } else if (CallInst *CI = dyn_cast<CallInst>(User)) {
    //   auto *callee = CI->getCalledFunction();
    //   if (!callee) {
    //     // indirect call, be conservative
    //     safe = false;
    //   } else {
    //     auto nargs = callee->arg_size();
    //     for (unsigned i = 0; i < nargs; i++) {
    //       if (CI->getArgOperand(i) == GEPI) {
    //         safe = false;
    //       }
    //     }
    //   }
    // }

    // NOTE: the above prevents tagged pointers from being returned, but it's
    // just a makeshift solution for a weird behavior present inside libstdc++
    // else errs() << "[HWASAN] GEP instrumentation: checking use in
    // instruction: " << *User
    //            << "\n\t resultLong: " << *resultLong << "\n\t GEPI: " <<
    //            *GEPI
    //            << "\n";
    return safe;
  });
  NumInstrumentedGEPs++;
  // NOTE: instrumented might also mean untagged
} // InstrumentGEP

void HWAddressSanitizer::InstrumentCMP(CmpInst *CI) {
  // EXAMPLE
  /**
   * %fImpl = getelementptr inbounds nuw
   * %"class.xercesc_2_7::DOM_NodeIterator", ptr %this, i32 0, i32 0, !dbg
   * !402 %0 = load ptr, ptr %fImpl, align 8, !dbg !402, !tbaa !325 %fImpl2 =
   * getelementptr inbounds nuw
   * %"class.xercesc_2_7::DOM_NodeIterator", ptr %other, i32 0, i32 0, !dbg
   * !403 %1 = load ptr, ptr %fImpl2, align 8, !dbg !403, !tbaa !325 %cmp =
   * icmp eq ptr %0, %1, !dbg !404
   */

  // NOTE: if one of the operands is null, no need to untag
  auto op1 = CI->getOperand(0);
  auto cmpType = op1->getType();
  auto op2 = CI->getOperand(1);
  // auto cmpType2 = op2->getType();
  // auto oneIsNull =
  //     isa<ConstantPointerNull>(op1) || isa<ConstantPointerNull>(op2);
  // if (oneIsNull)
  //   return;
  // NOTE: dont do this, it breaks 502.gcc_r. There is a tagged nullptr being
  // dereferenced.

  // NOTE CMP between pointers looks like this "icmp eq ptr %0, %1"
  if (cmpType->isPointerTy()) {
    IRBuilder<> IRB(CI);
    auto untaggedop1long = untagPointer(IRB, IRB.CreatePtrToInt(op1, IntptrTy));
    auto untaggedop2long = untagPointer(IRB, IRB.CreatePtrToInt(op2, IntptrTy));
    Value *untaggedPtr1 = IRB.CreateIntToPtr(untaggedop1long, cmpType);
    Value *untaggedPtr2 = IRB.CreateIntToPtr(untaggedop2long, cmpType);

    untaggedPtr1->setName("cmp_op1_untagged");
    untaggedPtr2->setName("cmp_op2_untagged");

    // Mark as volatile to prevent optimization folding --> this is not
    // verified if (Instruction *I1 = dyn_cast<Instruction>(untaggedPtr1))
    //   I1->setMetadata(LLVMContext::MD_mem_parallel_loop_access,
    //           MDNode::get(I1->getContext(), {}));
    // if (Instruction *I2 = dyn_cast<Instruction>(untaggedPtr2))
    //   I2->setMetadata(LLVMContext::MD_mem_parallel_loop_access,
    //           MDNode::get(I2->getContext(), {}));

    CI->replaceUsesOfWith(op1, untaggedPtr1);
    CI->replaceUsesOfWith(op2, untaggedPtr2);
    NumInstrumentedCMPs++;
    // DEBUG
    // FunctionType *PrintfTy = FunctionType::get(
    //     Type::getInt32Ty(M.getContext()),
    //     {PointerType::getUnqual(Type::getInt8Ty(M.getContext()))}, true);
    // FunctionCallee printfFunc = M.getOrInsertFunction("printf", PrintfTy);
    // IRBuilder<> IRBprintf(CI);
    // Value *formatStr = IRBprintf.CreateGlobalStringPtr(
    //     "[HWASAN][DEBUG] Instrumented CMP: %p vs %p -- %p %p\n");
    // Value *ptr1 = IRBprintf.CreatePointerCast(
    //     op1, PointerType::getUnqual(Type::getInt8Ty(M.getContext())));
    // Value *ptr2 = IRBprintf.CreatePointerCast(
    //     op2, PointerType::getUnqual(Type::getInt8Ty(M.getContext())));
    // IRBprintf.CreateCall(printfFunc, {formatStr, ptr1, ptr2, untaggedPtr1,
    // untaggedPtr2}); DEBUG END
  }
}

bool followOpDefUseChainForArithmetic(Value *V) {
  // When marking something as pointer, it must be a pointer OW we disrupt
  // integers.
  // bool isAllocaPtr = false;
  // isAllocaPtr = isa<AllocaInst>(V->stripPointerCasts());
  bool isCallReturn = isa<CallInst>(V->stripPointerCasts());
  if (isCallReturn) {
    errs() << " Following CallInst for Arithmetic Operand: " << *V << "\n";
    CallInst *CI = cast<CallInst>(V->stripPointerCasts());

    Function *CalledFunc = CI->getCalledFunction();

    if (CalledFunc) {
      if (CalledFunc->getReturnType()->isPointerTy()) {
        errs() << "  Call returns POINTER type: "
               << *(CalledFunc->getReturnType()) << "\n";
      } else {
        errs() << "  Call returns NON-POINTER type: "
               << *(CalledFunc->getReturnType()) << "\n";
      }
      auto demangledName = demangle(CalledFunc->getName().str());
      errs() << "  Demangled function name: " << demangledName << "\n";
      return CalledFunc->getReturnType()->isPointerTy() ||
             demangledName.find("std::__cxx11") == 0;
      // this can never work
      // 1. functions return i64 in place of ptrs
      // 2. even if it returns ptrs, -1 would be sminchiato
      // 3. how do you catch them all?
    }
  }
  if (dyn_cast<LoadInst>(V)) {
    LoadInst *LI = dyn_cast<LoadInst>(V);
    return LI->getType()->isPointerTy();
    // NOTE: you can also check for FieldArmor in the name.
  }
  if (dyn_cast<PtrToIntInst>(V)) {
    return true;
  }
  return isa<PtrToIntInst>(V);
}

void HWAddressSanitizer::InstrumentArithmetic(BinaryOperator *CI) {
  auto op1 = CI->getOperand(0);
  auto op2 = CI->getOperand(1);
  errs() << " Instrumenting Arithmetic Op: " << *CI << "\n";
  errs() << "  Operand 1: " << *op1 << "\n";
  errs() << "  Operand 2: " << *op2 << "\n";
  auto op1name = op1->hasName() ? op1->getName().str() : "";
  auto op2name = op2->hasName() ? op2->getName().str() : "";
  // err on the safe side, untag even if potentially untagged
  bool isPointerO1 = followOpDefUseChainForArithmetic(op1);
  bool isPointerO2 = followOpDefUseChainForArithmetic(op2);
  if (isPointerO1)
    errs() << "  Operand 1 is POINTER\n";
  if (isPointerO2)
    errs() << "  Operand 2 is POINTER\n";

  if (isPointerO1 || isPointerO2) {
    IRBuilder<> IRB(CI);

    if (isPointerO1) {
      Value *untaggedop1 = untagPointer(IRB, op1);
      untaggedop1->setName("arith_op1_untagged");
      CI->replaceUsesOfWith(op1, untaggedop1);
    }

    if (isPointerO2) {
      Value *untaggedop2 = untagPointer(IRB, op2);
      untaggedop2->setName("arith_op2_untagged");
      CI->replaceUsesOfWith(op2, untaggedop2);
    }
    // NumInstrumentedArithmeticOps++;
    CI->setName("arith_op_untagged");
    //   FunctionCallee printf = M.getOrInsertFunction(
    //     "printf",
    //     FunctionType::get(
    //         Type::getInt32Ty(M.getContext()),
    //         {PointerType::getUnqual(Type::getInt8Ty(M.getContext()))},
    //         true));
    // IRBuilder<> IRBprintf(CI);
    // Value *formatStr = IRBprintf.CreateGlobalStringPtr(
    //     "[HWASAN][DEBUG] Instrumented Arithmetic Op: %p -- %p %p\n");
    // Value *ptr1 = IRBprintf.CreatePointerCast(
    //     op1, PointerType::getUnqual(Type::getInt8Ty(M.getContext())));
    // Value *ptr2 = IRBprintf.CreatePointerCast(
    //     op2, PointerType::getUnqual(Type::getInt8Ty(M.getContext())));
    // IRBprintf.CreateCall(printf, {formatStr, CI, ptr1, ptr2});
  }
  // DEBUG

} // InstrumentArithmetic

void HWAddressSanitizer::InstrumentPtrToInt(PtrToIntInst *PI) {
  // TODO: ptrtoint on global is constexpr!!!!
  // TODO: instrument only if they are flowing into arithmetic instructions?
  // Q: where is ptrtoint used? Is it more convenient to instrument its users?
  // REPLACE ptr to int with untagged ptr to int
  // LLVM_DEBUG(dbgs() << "[FieldArmor] Instrumenting PtrToInt: " << *PI <<
  // "\n");
  IRBuilder<> IRB(PI->getNextNonDebugInstruction());
  // IRBuilder<> IRB(PI);
  // errs() << "Instrumenting PtrToInt: " << *PI << "\n";
  // errs() << " Operand: " << *(PI->getPointerOperand()) << "\n";
  // errs() << " Operand: " << *(PI->getOperand(0)) << "\n";

  // auto operand = PI->getPointerOperand();
  // Value* input = IRB.CreatePtrToInt(operand, PI->getType());
  // Value *untaggedPtr = untagPointer(IRB, input);
  // Value* tmp = IRB.CreateIntToPtr(untaggedPtr, operand->getType());
  // PI->setOperand(0, tmp);
  Value *untaggedPtr = IRB.CreateAnd(
      PI, ConstantInt::get(PI->getType(), ~(TagMaskByte << PointerTagShift)));
  // Value *semPtr = IRB.CreateAnd(untaggedPtr,
  //                            ConstantInt::get(PI->getType(),
  //                            0x00FFFFFFFFFFFFFFLu));
  // zero out MSB to preserve semantics
  // PROBLEM here: when 0xff is present at MSB, comparison with -1 fails in
  // switch stmt example (res == (void*)-1)
  // semPtr->setName(untaggedPtr->getName() + ".untagged_ptr_to_int");
  untaggedPtr->setName(".untagged_ptr_to_int");
  PI->replaceUsesWithIf(untaggedPtr, [PI, untaggedPtr](const Use &U) {
    auto *User = U.getUser();
    return User != PI && User != untaggedPtr && !isa<LifetimeIntrinsic>(User);
    // NOTE: semPtr does not use PI, it could go...
  });
  // Q: do I still need to replace the uses?
}

/** Only expect structs, arrays of structs, matrices of structs */
void HWAddressSanitizer::instrumentGlobal(GlobalVariable *GV) {
  Constant *Initializer = GV->getInitializer();
  Type *type = GV->getValueType();
  assert(type->isAggregateType() &&
         "[FieldArmor] Expected only aggregate types to be instrumented");

  bool isStruct = type->isStructTy();
  bool isArrayOfStructs =
      type->isArrayTy() &&
      dyn_cast<ArrayType>(type)->getArrayElementType()->isStructTy();

  bool isMatrixOfStructs =
      type->isArrayTy() &&
      dyn_cast<ArrayType>(type)->getElementType()->isArrayTy() &&
      dyn_cast<ArrayType>(dyn_cast<ArrayType>(type)->getElementType())
          ->getElementType()
          ->isStructTy();

  if (!(isStruct || isArrayOfStructs || isMatrixOfStructs)) {
    errs() << "[FieldArmor - WARNING] Skipping global variable: "
           << GV->getName() << "\n";
    errs() << *type << "\n";
    return;
  }

  bool isUnion = false;
  std::string struct_name = "";

  if (type->isStructTy()) {
    StructType *ST = dyn_cast<StructType>(type);
    if (ST->isLiteral()) {
      return;
    }
    isUnion = ST->getName().str().find("union.") != std::string::npos;
    struct_name = ST->getName().str();
  }

  if (isArrayOfStructs) {
    Type *elementType = type->getArrayElementType();
    StructType *STA = dyn_cast<StructType>(elementType);
    if (STA->isLiteral())
      return;
    isUnion = STA->getName().str().find("union.") != std::string::npos;
    struct_name = STA->getName().str();
  }

  if (isMatrixOfStructs) {
    Type *elementType = dyn_cast<ArrayType>(type)->getElementType();
    Type *structType = dyn_cast<ArrayType>(elementType)->getElementType();
    StructType *STM = dyn_cast<StructType>(structType);
    if (STM->isLiteral())
      return;
    isUnion = STM->getName().str().find("union.") != std::string::npos;
    struct_name = STM->getName().str();
  }

  if (isUnion)
    return;

  uint64_t SizeInBytes =
      M.getDataLayout().getTypeAllocSize(Initializer->getType());

  auto *NewGV = new GlobalVariable(M, Initializer->getType(), GV->isConstant(),
                                   GlobalValue::ExternalLinkage, Initializer,
                                   GV->getName() + ".hwasan");
  NewGV->copyAttributesFrom(GV);
  NewGV->setLinkage(GlobalValue::PrivateLinkage);
  NewGV->copyMetadata(GV, 0);
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
  // NOTE: the new global is actually the symbol that gets loaded on each use
  // of the former global

  // NOTE: dont set tag vector here, do it once and for all in constructor and
  // only reference it here

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

    assert(!struct_name.empty() &&
           "Struct name must be valid to instrument global variable.");

    auto *TagVector =
        M.getGlobalVariable(struct_name + ".fieldarmor.tagvec", true);

    if (TagVector == nullptr) {
      // NOTE: this fails for arrays of pairs
      errs() << "[FieldArmor] Error: Tag vector global not found for struct: "
             << struct_name << "\n";
      errs() << *GV << "\n";
      errs() << *type << "\n";
      errs() << "isStructTy()? " << type->isStructTy() << "\n";
      errs() << "isArrayTy()? " << type->isArrayTy() << "\n";
      errs() << "isMatrixOfStructs? " << isMatrixOfStructs << "\n";
      errs() << "isArrayOfStructs? " << isArrayOfStructs << "\n";
      errs() << "isLiteral? "
             << (type->isStructTy() ? dyn_cast<StructType>(type)->isLiteral()
                                    : false)
             << "\n";
      errs() << "isOpaque? "
             << (type->isStructTy() ? dyn_cast<StructType>(type)->isOpaque()
                                    : false)
             << "\n";
      errs() << "isSized?"
             << (type->isStructTy() ? dyn_cast<StructType>(type)->isSized()
                                    : false)
             << "\n";
      assert(TagVector &&
             "Tag vector global must exist and be properly initialized.");
    }
    auto *TVRelPtr = ConstantExpr::getTrunc(
        ConstantExpr::getSub(ConstantExpr::getPtrToInt(TagVector, Int64Ty),
                             ConstantExpr::getPtrToInt(Descriptor, Int64Ty)),
        Int32Ty);
    // auto *arraySize = ConstantInt::get(
    //     Int32Ty, 0x1); // fix to this value for now!!! TODO :REMOVE
    Constant *arraySize = nullptr;
    if (isStruct) {
      // single struct
      arraySize = ConstantInt::get(
          Int32Ty, 0x1); // fix to this value for now!!! TODO :REMOVE
      ;
    } else {
      // array of structs
      if (isMatrixOfStructs) {
        auto outerArrayType = dyn_cast<ArrayType>(type);
        auto innerArrayType =
            dyn_cast<ArrayType>(outerArrayType->getElementType());
        assert(outerArrayType &&
               "Outer array type must be valid for matrix of structs.");
        assert(innerArrayType &&
               "Inner array type must be valid for matrix of structs.");

        arraySize =
            ConstantInt::get(Int32Ty, outerArrayType->getNumElements() *
                                          innerArrayType->getNumElements());
      } else {
        auto arrayType = dyn_cast<ArrayType>(type);
        arraySize = ConstantInt::get(Int32Ty, arrayType->getNumElements());
      }
    }
    assert(arraySize && "Array size constant must be valid.");
    uint32_t Size = std::min(SizeInBytes - DescriptorPos, MaxDescriptorSize);
    auto *SizeAndTag = ConstantInt::get(Int32Ty, Size);
    Descriptor->setComdat(NewGV->getComdat());
    Descriptor->setInitializer(
        ConstantStruct::getAnon({GVRelPtr, SizeAndTag, TVRelPtr, arraySize}));
    Descriptor->setSection("hwasan_globals");
    Descriptor->setMetadata(LLVMContext::MD_associated,
                            MDNode::get(*C, ValueAsMetadata::get(NewGV)));
    // Descriptor->setAlignment(Align(16)); // doesnt really matter
    appendToCompilerUsed(M, Descriptor);
  }

  // uint8_t Tag = 0b10000000U;
  uint8_t Tag = RPTag; // global tags must be handled carefully, the linker does
                       // not know how to relocate it if the MSB is set!!!
  // in the asm, this gets evaluated to 2^^32. The linker, subsequently, does
  // the relocation magic and replaces that with something else like the thing
  // down here
  Constant *Aliasee = ConstantExpr::getIntToPtr(
      ConstantExpr::getAdd(
          ConstantExpr::getPtrToInt(NewGV, Int64Ty),
          ConstantInt::get(Int64Ty, (uint64_t)(Tag) << PointerTagShift)),
      GV->getType()); // NOTE: this does not work!!!!! Ptrs cannot be tagged
                      // this way because it breaks global references
  auto *Alias = GlobalAlias::create(GV->getValueType(), GV->getAddressSpace(),
                                    GV->getLinkage(), "", Aliasee, &M);
  Alias->setVisibility(GV->getVisibility());
  Alias->takeName(GV);
  GV->replaceAllUsesWith(Alias); /// WRONG!
  // uses must be replaced with tag only if they are not in some arithmetic
  // instruction
  GV->eraseFromParent();
  NumInstrumentedGlobals++;
} // instrumentGlobal

void HWAddressSanitizer::instrumentGlobals() {
  std::vector<GlobalVariable *> Globals;

  for (GlobalVariable &GV : M.globals()) {

    if (GV.hasSanitizerMetadata() && GV.getSanitizerMetadata().NoHWAddress)
      continue;

    if (GV.isDeclarationForLinker() || GV.getName().starts_with("llvm.") ||
        GV.isThreadLocal())
      continue;

    // Common symbols can't have aliases point to them, so they can't be
    // tagged.
    if (GV.hasCommonLinkage())
      continue;
    /** NOTE: do not instrument tag vectors, they are special globals */
    if (GV.getName().contains("tagvec"))
      continue;
    // Globals with custom sections may be used in __start_/__stop_
    // enumeration, which would be broken both by adding tags and
    // potentially by the extra padding/alignment that we insert.
    if (GV.hasSection())
      continue;
    // WHAT HAPPEN IF A GLOBAL HAS NO INITIALIZER?

    if (GV.getValueType()->isArrayTy()) {
      if (!GV.getValueType()->getArrayElementType()->isStructTy() &&
          !GV.getValueType()->getArrayElementType()->isArrayTy()) {
        // array of structs
        continue;
      } else if (GV.getValueType()->getArrayElementType()->isArrayTy()) {
        ArrayType *elemArrayType =
            dyn_cast<ArrayType>(GV.getValueType()->getArrayElementType());
        if (!elemArrayType->getElementType()->isStructTy()) {
          // skipping 3d array
          errs() << "[HWASAN] Skipping global variable (3D array): "
                 << GV.getName() << "\n";
          continue;
        } // arrays of arrays of something other than structs
        else if (elemArrayType->getElementType()->isStructTy()) {
          bool isLiteral = dyn_cast<StructType>(elemArrayType->getElementType())
                               ->isLiteral();
          bool isUnion =
              isLiteral ? true
                        : dyn_cast<StructType>(elemArrayType->getElementType())
                                  ->getName()
                                  .str()
                                  .find("union.") == 0;
          if (isUnion || isLiteral) {
            continue;
          }
        } // if array of arrays of structs
      } // if array of arrays
    } // if it's an array

    else if (!GV.getValueType()->isStructTy()) {
      continue;
    } // Q: can I do the check on the initializer? Or it breaks?

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
    if (any_of(P.second, [](const Function *F) {
          return F->hasFnAttribute("branch-target-enforcement");
        })) {
      ThunkFn->addFnAttr("branch-target-enforcement");
    }
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
  //   // Fuchsia is always PIE, which means that the beginning of the address
  //   // space is always available.
  //   SetFixed(0);
  // } else

  if (CompileKernel || InstrumentWithCalls) {
    SetFixed(0);
    WithFrameRecord = false;
  }
  // TODO: invest some time in figuring out this
  WithFrameRecord = optOr(ClFrameRecords, WithFrameRecord);

  // Apply the last of ClMappingOffset and ClMappingOffsetDynamic.
  Kind = optOr(ClMappingOffsetDynamic, Kind);
  if (ClMappingOffset.getNumOccurrences() > 0 &&
      !(ClMappingOffsetDynamic.getNumOccurrences() > 0 &&
        ClMappingOffsetDynamic.getPosition() > ClMappingOffset.getPosition())) {
    SetFixed(ClMappingOffset);
  }
}

Value *HWAddressSanitizer::getRPTag(IRBuilder<> &IRB) {
  return ConstantInt::get(Int64Ty, RPTag);
}

/** This method is called on whatever struct that was identified in the
 * frontend. This includes unions and literal structs. */
void HWAddressSanitizer::createTagVector(StructType *t) {
  // dont create if it already exists
  std::string TagVecName = t->getStructName().str() + ".fieldarmor.tagvec";
  auto *TagVec = M.getGlobalVariable(TagVecName, true);
  if (TagVec) {
    errs() << "[FieldArmor] Tag vector " << TagVecName
           << " already exists, skipping creation.\n";
    return;
  }
  auto size = M.getDataLayout().getTypeAllocSize(t);

  u_int8_t *tags = nullptr;
  bool isLiteral = t->isLiteral();
  bool isUnion =
      !isLiteral && t->getName().str().find("union.") != std::string::npos;

  if (isLiteral || isUnion) {
    /** Non-literal union: treat it as a scalar field. */
    tags = new uint8_t[size];
    memset(tags, (unsigned char)0x00, size);
  } else {
    tags = computeTags(t);
  }

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
  appendToCompilerUsed(M, NewTagVector_global);
  // errs() << "[FieldArmor] Created tag vector " << TagVecName << "\n";
  NumDefinedTagVectors++;
}

void HWAddressSanitizer::createTagVectors() {
  auto identifiedStructTypes = M.getIdentifiedStructTypes();
  // for (auto t : identifiedStructTypes)
  //   errs() << "[FieldArmor] Identified StructType: " << *t << "\n";

  for (auto t : identifiedStructTypes) {
    StructType *ty = dyn_cast<StructType>(t);
    // errs() << "[FieldArmor] Creating tag vector for StructType " << *t <<
    // "\n";
    /** NOTE: opaque types are not sized. */
    if (!ty->isSized()) {
      // Q: what is the solution to this?
      errs() << "[FieldArmor] StructType " << *t << " is not sized!\n";
      continue;
    }

    createTagVector(t);
  }
}

/** This method computes tags for aggregates of unions up to level 2
 * (matrices). Vectors are out of scope for now. */
u_int8_t *HWAddressSanitizer::computeTags(StructType *Ty) {
  // TODO: introduce ad hoc tag for padding (maybe 0xff?)
  // TODO: try tagging unions
  // TODO: remove the 0 tag from everywhere else
  // TODO: measure coverage of literal structs
  DataLayout DL = M.getDataLayout();
  u_int8_t *tags = new u_int8_t[DL.getTypeAllocSize(Ty)];
  memset(tags, 0, DL.getTypeAllocSize(Ty));

  assert(tags && "Could not allocate tags array");
  std::deque<std::tuple<Type *, uint8_t, uint8_t, uint8_t, size_t>> AggQueue;

  auto levelZeroFieldsOffsets = DL.getStructLayout(Ty)->getMemberOffsets();

  uint8_t fatherT = 0;
  uint8_t fatherL = 0;
  uint16_t sonIdx = 1; // NOTE: 2^^16 max number of fields because tag on 4 bits
  if (levelZeroFieldsOffsets.size() >= (1 << 16) - 1) {
    /** Too many fields :( */
    errs() << "[FieldArmor] Struct " << *Ty
           << " has too many fields to be tagged properly.\n";
    return nullptr;
  }

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
    // auto isClass = ST_son && !isLitStr && !isUnion &&
    //                (ST_son->getName().find("class.") == 0);
    // TODO: if a class is embedded in a struct and the class has padding in the
    // end, that is treated as an extra field and can lead to FPs? This has
    // never happened till now.
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
        auto tagVectorGlobal =
            M.getGlobalVariable(structName + ".fieldarmor.tagvec", true);

        if (!tagVectorGlobal)
          createTagVector(structType);

        tagVectorGlobal =
            M.getGlobalVariable(structName + ".fieldarmor.tagvec", true);

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
          // vector is used? E.g. base vs non-base? Using struct size should be
          // fine though.

          auto structName = structType->getStructName().str();
          auto tagVectorGlobal =
              M.getGlobalVariable(structName + ".fieldarmor.tagvec", true);

          if (!tagVectorGlobal) {
            createTagVector(structType);
          }
          tagVectorGlobal =
              M.getGlobalVariable(structName + ".fieldarmor.tagvec", true);

          if (!tagVectorGlobal) {
            continue; // you could assert it here
          }
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
        // DEBUG
        // errs() << "[FieldArmor - WARNING] Treating as scalar EMBEDDED
        // struct
        // "
        //           "field: ";
        // errs() << *ty << "\n";
        // errs() << "container " << *Ty << "\n";
        // errs() << "is opaque " << (ty->isOpaque() ? "true" : "false") <<
        // "\n"; errs() << "is literal " << (ty->isLiteral() ? "true" :
        // "false")
        // << "\n"; if (!ty->isLiteral())
        //   errs() << "is union "
        //          << ((ty->getName().str().find("union.") == 0) ? "true"
        //                                                        : "false")
        //          << "\n";
        // if (!ty->isLiteral())
        //   errs() << "struct name " << ty->getName().str() << "\n";
        // EDN DEBUG
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

/**
 * GEPs on globals are constant expr, right? Maybe not ...
 */
void HWAddressSanitizer::InstrumentConstGEP(ConstantExpr *GEPI) {
  errs() << "[FieldArmor] Instrumenting CONST GEP: ";
  GEPI->print(errs());
  errs() << "\n";

  auto nOperands = GEPI->getNumOperands();
  assert(nOperands <= 3); // I expect 3 at most
  if (nOperands == 2) {
    errs() << "[FieldArmor] WARNING: CONST GEP with 2 operands found: ";
    GEPI->print(errs());
    errs() << "\n";
    return;
  }
} // instrumentConstGEP