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
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/BinaryFormat/ELF.h"
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

static const size_t kDefaultShadowScale = 0; // HWAsanIO 0

static const unsigned kShadowBaseAlignment = 32;

namespace {
enum class OffsetKind {
  kFixed = 0,
  kGlobal,
  kIfunc,
  kTls,
};
}

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
                                       cl::Hidden, cl::init(true));

static cl::opt<bool>
    ClRecover("hwasan-recover",
              cl::desc("Enable recovery mode (continue-after-error)."),
              cl::Hidden, cl::init(false));

static cl::opt<bool> ClInstrumentStack("hwasan-instrument-stack",
                                       cl::desc("instrument stack (allocas)"),
                                       cl::Hidden, cl::init(true));

static cl::opt<bool>
    ClUseStackSafety("hwasan-use-stack-safety", cl::Hidden, cl::init(true),
                     cl::Hidden, cl::desc("Use Stack Safety analysis results"),
                     cl::Optional);

static cl::opt<size_t> ClMaxLifetimes(
    "hwasan-max-lifetimes-for-alloca", cl::Hidden, cl::init(3),
    cl::ReallyHidden,
    cl::desc("How many lifetime ends to handle for a single alloca."),
    cl::Optional);

static cl::opt<bool>
    ClUseAfterScope("hwasan-use-after-scope",
                    cl::desc("detect use after scope within function"),
                    cl::Hidden, cl::init(false)); // fuck this

static cl::opt<bool> ClGenerateTagsWithCalls(
    "hwasan-generate-tags-with-calls",
    cl::desc("generate new tags with runtime library calls"), cl::Hidden,
    cl::init(false));

static cl::opt<bool> ClGlobals("hwasan-globals", cl::desc("Instrument globals"),
                               cl::Hidden, cl::init(false));

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

static cl::opt<float>
    ClRandomKeepRate("hwasan-random-rate",
                     cl::desc("Probability value in the range [0.0, 1.0] "
                              "to keep instrumentation of a function. "
                              "Note: instrumentation can be skipped randomly "
                              "OR because of the hot percentile cutoff, if "
                              "both are supplied."));

STATISTIC(NumTotalFuncs, "Number of total funcs");
STATISTIC(NumInstrumentedFuncs, "Number of instrumented funcs");
STATISTIC(NumNoProfileSummaryFuncs, "Number of funcs without PS");
// STATISTIC(NumGEPInstrumented, "Number of GEPs instrumented");
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

static cl::opt<RecordStackHistoryMode> ClRecordStackHistory(
    "hwasan-record-stack-history",
    cl::desc("Record stack frames with tagged allocations in a thread-local "
             "ring buffer"),
    cl::values(clEnumVal(none, "Do not record stack ring history"),
               clEnumVal(instr, "Insert instructions into the prologue for "
                                "storing into the stack ring buffer directly"),
               clEnumVal(libcall, "Add a call to __hwasan_add_frame_record for "
                                  "storing into the stack ring buffer")),
    cl::Hidden, cl::init(instr));

static cl::opt<bool>
    ClInstrumentMemIntrinsics("hwasan-instrument-mem-intrinsics",
                              cl::desc("instrument memory intrinsics"),
                              cl::Hidden, cl::init(true));

static cl::opt<bool>
    ClInstrumentLandingPads("hwasan-instrument-landing-pads",
                            cl::desc("instrument landing pads"), cl::Hidden,
                            cl::init(false));

static cl::opt<bool> ClUseShortGranules(
    "hwasan-use-short-granules",
    cl::desc("use short granules in allocas and outlined checks"), cl::Hidden,
    cl::init(false)); // this is disabled so it shouldn't be a problem

static cl::opt<bool> ClInstrumentPersonalityFunctions(
    "hwasan-instrument-personality-functions",
    cl::desc("instrument personality functions"), cl::Hidden);

static cl::opt<bool> ClInlineAllChecks("hwasan-inline-all-checks",
                                       cl::desc("inline all checks"),
                                       cl::Hidden, cl::init(false));

static cl::opt<bool> ClInlineFastPathChecks("hwasan-inline-fast-path-checks",
                                            cl::desc("inline all checks"),
                                            cl::Hidden, cl::init(false));

// Enabled from clang by "-fsanitize-hwaddress-experimental-aliasing".
static cl::opt<bool> ClUsePageAliases("hwasan-experimental-use-page-aliases",
                                      cl::desc("Use page aliasing in HWASan"),
                                      cl::Hidden, cl::init(false));

namespace {

template <typename T> T optOr(cl::opt<T> &Opt, T Other) {
  return Opt.getNumOccurrences() ? Opt : Other;
}

bool shouldUsePageAliases(const Triple &TargetTriple) {
  return ClUsePageAliases && TargetTriple.getArch() == Triple::x86_64;
}

bool shouldInstrumentStack(const Triple &TargetTriple) {
  return !shouldUsePageAliases(TargetTriple) && ClInstrumentStack;
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

bool shouldDetectUseAfterScope(const Triple &TargetTriple) { // TODO remove this
  return ClUseAfterScope && shouldInstrumentStack(TargetTriple);
}

/// An instrumentation pass implementing detection of addressability bugs
/// using tagged pointers.
class HWAddressSanitizer {
public:
  HWAddressSanitizer(Module &M, bool CompileKernel, bool Recover,
                     const StackSafetyGlobalInfo *SSI)
      : M(M), SSI(SSI) {
    this->Recover = optOr(ClRecover, Recover);
    this->CompileKernel = optOr(ClEnableKhwasan, CompileKernel);
    this->Rng = ClRandomKeepRate.getNumOccurrences() ? M.createRNG(DEBUG_TYPE)
                                                     : nullptr;

    initializeModule();
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
  // FieldArmor
  // SetVector<GetElementPtrInst *> GEPsToInstrument; // TODO handle ConstGEPs?
  void InstrumentGEP(GetElementPtrInst *GEPI);    // TODO
  Value *isMemoryTagged(GetElementPtrInst *GEPI); // TODO
  Value *getAllocaTagRootPtr(IRBuilder<> &IRB, Value *StackTag,
                             unsigned AllocaNo); // TODO
  void
  ApplyRLT(IRBuilder<> &IRB, Instruction *AI, Type *rootType, Value *Tag,
           const DataLayout &DL); // should AI be a Value or an instruction?

  unsigned long long instrumentedGEPs = 0;
  // END FieldArmor
  bool selectiveInstrumentationShouldSkip(Function &F,
                                          FunctionAnalysisManager &FAM) const;
  void initializeModule();
  void createHwasanCtorComdat();

  void initializeCallbacks(Module &M);

  Value *getOpaqueNoopCast(IRBuilder<> &IRB, Value *Val);

  Value *getDynamicShadowIfunc(IRBuilder<> &IRB);
  Value *getShadowNonTls(IRBuilder<> &IRB);

  void untagPointerOperand(Instruction *I, Value *Addr);
  Value *memToShadow(Value *Shadow, IRBuilder<> &IRB);

  int64_t getAccessInfo(bool IsWrite, unsigned AccessSizeIndex);
  ShadowTagCheckInfo insertShadowTagCheck(Value *Ptr, Instruction *InsertBefore,
                                          DomTreeUpdater &DTU, LoopInfo *LI);
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

  void tagAlloca(IRBuilder<> &IRB, AllocaInst *AI, Value *Tag, size_t Size,
                 const DataLayout &DL);
  Value *tagPointer(IRBuilder<> &IRB, Type *Ty, Value *PtrLong, Value *Tag);
  Value *untagPointer(IRBuilder<> &IRB, Value *PtrLong);
  bool instrumentStack(memtag::StackInfo &Info, Value *StackTag,
                       const DominatorTree &DT, const PostDominatorTree &PDT,
                       const LoopInfo &LI, const DataLayout &DL);
  bool instrumentLandingPads(SmallVectorImpl<Instruction *> &RetVec);
  Value *getNextTagWithCall(IRBuilder<> &IRB);
  Value *getStackBaseTag(IRBuilder<> &IRB);
  Value *getAllocaTag(IRBuilder<> &IRB, Value *StackTag, unsigned AllocaNo);
  Value *getUARTag(IRBuilder<> &IRB);

  Value *getHwasanThreadSlotPtr(IRBuilder<> &IRB);
  Value *applyTagMask(IRBuilder<> &IRB, Value *OldTag);
  unsigned retagMask(unsigned AllocaNo);

  void emitPrologue(IRBuilder<> &IRB, bool WithFrameRecord);

  void instrumentGlobal(GlobalVariable *GV, uint8_t Tag);
  void instrumentGlobalAggregate(GlobalVariable *GV, uint8_t Tag,
                                 const DataLayout &DL);
  void instrumentGlobals();

  Value *getCachedFP(IRBuilder<> &IRB);
  Value *getFrameRecordInfo(IRBuilder<> &IRB);

  void instrumentPersonalityFunctions();

  LLVMContext *C;
  Module &M;
  const StackSafetyGlobalInfo *SSI;
  Triple TargetTriple;
  std::unique_ptr<RandomNumberGenerator> Rng;

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
      errs() << "HWAddressSanitizer::ShadowMapping::SetFixed: O=" << O
             << "\n"; // this should not be the case
      Kind = OffsetKind::kFixed;
      Offset = O;
    }

  public:
    void init(Triple &TargetTriple, bool InstrumentWithCalls,
              bool CompileKernel);
    Align getObjectAlignment() const {
      return Align(1ULL << Scale);
    } // TODO: wtf does this do?
    bool isInGlobal() const { return Kind == OffsetKind::kGlobal; }
    bool isInIfunc() const { return Kind == OffsetKind::kIfunc; }
    bool isInTls() const { return Kind == OffsetKind::kTls; }
    bool isFixed() const { return Kind == OffsetKind::kFixed; }
    uint8_t scale() const { return Scale; };
    uint64_t offset() const {
      errs() << "HWAddressSanitizer::ShadowMapping::offset: Offset=" << Offset
             << "\n";
      errs() << "Is fixed? " << isFixed() << "\n";
      errs() << "Kind=" << (int)Kind << "\n";
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
  bool UseShortGranules;
  bool InstrumentLandingPads;
  bool InstrumentWithCalls;
  bool InstrumentStack;
  bool InstrumentGlobals;
  bool globalsInstrumented = false; // FieldArmor
  bool DetectUseAfterScope;
  bool UsePageAliases;
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
  Value *StackBaseTag = nullptr;
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
  const Triple &TargetTriple = M.getTargetTriple();
  if (shouldUseStackSafetyAnalysis(TargetTriple, Options.DisableOptimization))
    SSI = &MAM.getResult<StackSafetyGlobalAnalysis>(M);

  HWAddressSanitizer HWASan(M, Options.CompileKernel, Options.Recover, SSI);
  auto &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

  for (Function &F : M)
    HWASan.sanitizeFunction(F, FAM);
  LLVM_DEBUG(dbgs() << "HWAddressSanitizer: done instrumenting module\n");
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
  LLVM_DEBUG(dbgs() << "Init " << M.getName() << "\n");
  TargetTriple = M.getTargetTriple();

  // HWASan may do short granule checks on function arguments read from the
  // argument memory (last byte of the granule), which invalidates writeonly.
  for (Function &F : M.functions())
    removeASanIncompatibleFnAttributes(F, /*ReadsArgMem=*/true);

  // x86_64 currently has two modes:
  // - Intel LAM (default)
  // - pointer aliasing (heap only)
  bool IsX86_64 = TargetTriple.getArch() == Triple::x86_64;
  UsePageAliases = shouldUsePageAliases(TargetTriple);
  InstrumentWithCalls = shouldInstrumentWithCalls(TargetTriple);
  InstrumentStack = shouldInstrumentStack(TargetTriple);
  DetectUseAfterScope = shouldDetectUseAfterScope(TargetTriple);
  PointerTagShift = IsX86_64 ? 57 : 56;
  TagMaskByte = IsX86_64 ? 0x3F : 0xFF;
  errs() << "[+++] Summary of the initialization of HWAddressSanitizer\n";
  errs() << "TargetTriple: " << TargetTriple.str() << "\n";
  errs() << "IsX86_64: " << IsX86_64 << "\n";
  errs() << "UsePageAliases: " << UsePageAliases << "\n";
  errs() << "InstrumentWithCalls: " << InstrumentWithCalls << "\n";
  errs() << "InstrumentStack: " << InstrumentStack << "\n";
  errs() << "DetectUseAfterScope: " << DetectUseAfterScope << "\n";
  errs() << "PointerTagShift: " << PointerTagShift << "\n";
  errs() << "TagMaskByte: " << (unsigned)TagMaskByte << "\n";
  errs() << "______________________________________________________\n";

  Mapping.init(TargetTriple, InstrumentWithCalls, CompileKernel);

  C = &(M.getContext());
  IRBuilder<> IRB(*C);

  HwasanCtorFunction = nullptr;

  // Older versions of Android do not have the required runtime support for
  // short granules, global or personality function instrumentation. On other
  // platforms we currently require using the latest version of the runtime.
  bool NewRuntime =
      !TargetTriple.isAndroid() || !TargetTriple.isAndroidVersionLT(30);

  // UseShortGranules = optOr(ClUseShortGranules, NewRuntime);
  UseShortGranules = false; // TODO CHECK
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

  InstrumentGlobals =
      !CompileKernel && !UsePageAliases && optOr(ClGlobals, NewRuntime);

  if (!CompileKernel) {
    createHwasanCtorComdat(); // creates the routine ctor with a call into the
                              // runtime function __hwasan_init

    if (InstrumentGlobals)
      instrumentGlobals(); // sets up global instrumentation

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

  if (isa<GlobalVariable>(getUnderlyingObject(Ptr))) {
    if (!InstrumentGlobals)
      return true;
    // TODO: Optimize inbound global accesses, like Asan `instrumentMop`.
  }

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
    if (!ClInstrumentReads || ignoreAccess(ORE, I, LI->getPointerOperand()))
      return;
    Interesting.emplace_back(I, LI->getPointerOperandIndex(), false,
                             LI->getType(), LI->getAlign());
  } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
    if (!ClInstrumentWrites || ignoreAccess(ORE, I, SI->getPointerOperand()))
      return;
    Interesting.emplace_back(I, SI->getPointerOperandIndex(), true,
                             SI->getValueOperand()->getType(), SI->getAlign());
  } else if (AtomicRMWInst *RMW = dyn_cast<AtomicRMWInst>(I)) {
    if (!ClInstrumentAtomics || ignoreAccess(ORE, I, RMW->getPointerOperand()))
      return;
    Interesting.emplace_back(I, RMW->getPointerOperandIndex(), true,
                             RMW->getValOperand()->getType(), std::nullopt);
  } else if (AtomicCmpXchgInst *XCHG = dyn_cast<AtomicCmpXchgInst>(I)) {
    if (!ClInstrumentAtomics || ignoreAccess(ORE, I, XCHG->getPointerOperand()))
      return;
    Interesting.emplace_back(I, XCHG->getPointerOperandIndex(), true,
                             XCHG->getCompareOperand()->getType(),
                             std::nullopt);
  } else if (auto *CI = dyn_cast<CallInst>(I)) {
    for (unsigned ArgNo = 0; ArgNo < CI->arg_size(); ArgNo++) {
      if (!ClInstrumentByval || !CI->isByValArgument(ArgNo) ||
          ignoreAccess(ORE, I, CI->getArgOperand(ArgNo)))
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
  assert(!UsePageAliases);
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
    IRB.CreateIntrinsic(
        UseShortGranules
            ? Intrinsic::hwasan_check_memaccess_shortgranules_fixedshadow
            : Intrinsic::hwasan_check_memaccess_fixedshadow,
        {Ptr, ConstantInt::get(Int32Ty, AccessInfo),
         ConstantInt::get(Int64Ty, Mapping.offset())});
  } else {
    IRB.CreateIntrinsic(
        UseShortGranules ? Intrinsic::hwasan_check_memaccess_shortgranules
                         : Intrinsic::hwasan_check_memaccess,
        {ShadowBase, Ptr, ConstantInt::get(Int32Ty, AccessInfo)});
  }
}

void HWAddressSanitizer::instrumentMemAccessInline(Value *Ptr, bool IsWrite,
                                                   unsigned AccessSizeIndex,
                                                   Instruction *InsertBefore,
                                                   DomTreeUpdater &DTU,
                                                   LoopInfo *LI) {
  assert(!UsePageAliases);
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
  errs() << "[++] Instrumenting memory intrinsic: " << *MI << "\n";
  IRBuilder<> IRB(MI);
  if (isa<MemTransferInst>(MI)) { /*memcpy, memmove*/
    SmallVector<Value *, 4> Args{
        MI->getOperand(0), MI->getOperand(1),
        IRB.CreateIntCast(MI->getOperand(2), IntptrTy, false)};

    if (UseMatchAllCallback)
      Args.emplace_back(ConstantInt::get(Int8Ty, *MatchAllTag));
    IRB.CreateCall(isa<MemMoveInst>(MI) ? HwasanMemmove : HwasanMemcpy, Args);
  } else if (isa<MemSetInst>(MI)) {
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
  Value *Addr = O.getPtr();

  LLVM_DEBUG(dbgs() << "{++] Instrumenting MEMACCESS ");
  LLVM_DEBUG(O.getInsn()->print(dbgs()));
  LLVM_DEBUG(dbgs() << "\n");
  LLVM_DEBUG(O.OpType->print(dbgs()));

  if (O.OpType->isPointerTy()) {
    auto instruction = O.getInsn();
    if (dyn_cast<LoadInst>(instruction)) {
      LoadInst *LI = cast<LoadInst>(instruction);
      LLVM_DEBUG(dbgs() << " -> load instruction\n");
      LLVM_DEBUG(dbgs() << "load type: ");
      LLVM_DEBUG(LI->getType()->print(dbgs()));
    } else if (dyn_cast<StoreInst>(instruction)) {
      LLVM_DEBUG(dbgs() << " -> store instruction\n");
    } else {
      LLVM_DEBUG(dbgs() << " -> other instruction\n");
    }
  }
  LLVM_DEBUG(dbgs() << "\n");

  // If the pointer is statically known to be zero, the tag check will pass
  // since:
  // 1) it has a zero tag
  // 2) the shadow memory corresponding to address 0 is initialized to zero and
  //    never updated.
  // We can therefore elide the tag check.
  llvm::KnownBits Known(DL.getPointerTypeSizeInBits(Addr->getType()));
  llvm::computeKnownBits(Addr, Known, DL);
  if (Known.isZero())
    return false;

  if (O.MaybeMask)
    return false; // FIXME

  IRBuilder<> IRB(O.getInsn());
  if (!O.TypeStoreSize.isScalable() && isPowerOf2_64(O.TypeStoreSize) &&
      (O.TypeStoreSize / 8 <= (1ULL << (kNumberOfAccessSizes - 1))) &&
      (!O.Alignment || *O.Alignment >= Mapping.getObjectAlignment() ||
       *O.Alignment >= O.TypeStoreSize / 8)) {
    size_t AccessSizeIndex = TypeSizeToSizeIndex(O.TypeStoreSize);
    if (InstrumentWithCalls) {
      LLVM_DEBUG(dbgs() << "Using call-based instrumentation\n");
      SmallVector<Value *, 2> Args{IRB.CreatePointerCast(Addr, IntptrTy)};
      if (UseMatchAllCallback)
        Args.emplace_back(ConstantInt::get(Int8Ty, *MatchAllTag));
      IRB.CreateCall(HwasanMemoryAccessCallback[O.IsWrite][AccessSizeIndex],
                     Args);
    } else if (OutlinedChecks) {
      LLVM_DEBUG(dbgs() << "Outlining the check\n");
      instrumentMemAccessOutline(Addr, O.IsWrite, AccessSizeIndex, O.getInsn(),
                                 DTU, LI);
    } else {
      LLVM_DEBUG(dbgs() << "Inlining the check\n");
      instrumentMemAccessInline(Addr, O.IsWrite, AccessSizeIndex, O.getInsn(),
                                DTU, LI);
    }
  } else {
    LLVM_DEBUG(dbgs() << "Using call-based instrumentation, else case\n");
    SmallVector<Value *, 3> Args{
        IRB.CreatePointerCast(Addr, IntptrTy),
        IRB.CreateUDiv(IRB.CreateTypeSize(IntptrTy, O.TypeStoreSize),
                       ConstantInt::get(IntptrTy, 8))};
    if (UseMatchAllCallback)
      Args.emplace_back(ConstantInt::get(Int8Ty, *MatchAllTag));
    IRB.CreateCall(HwasanMemoryAccessCallbackSized[O.IsWrite], Args);
  }
  untagPointerOperand(O.getInsn(), Addr);

  return true;
}

uint8_t rotateOn4bits(uint8_t val, uint8_t positions) {
  positions = positions % 4;
  LLVM_DEBUG(dbgs() << " Rotating value: 0x" << utohexstr((unsigned)val)
                    << " by " << (unsigned)positions << " positions\n");
  val = ((val << positions) | (val >> (4 - positions)));
  LLVM_DEBUG(dbgs() << " Rotated value: 0x" << utohexstr((unsigned)val)
                    << "\n");
  assert(val >> 4 == 0 && "Rotation on 4 bits failed");
  return val;
}

void debugAggregateVisit(Type *sonType, uint8_t currNestingLevel,
                         uint8_t expectedTag, uint8_t typeMask,
                         uint8_t newBaseTag) {
  LLVM_DEBUG(dbgs() << " [RLT-DBG] AGGREGATE VISIT: ");
  LLVM_DEBUG(sonType->print(dbgs()));
  LLVM_DEBUG(dbgs() << "\n\tnesting level -> : " << (unsigned)currNestingLevel
                    << "\n");
  LLVM_DEBUG(dbgs() << "\texpected tag: 0x" << utohexstr((unsigned)expectedTag)
                    << "\n");
  LLVM_DEBUG(dbgs() << " \ttype mask: 0x" << utohexstr((unsigned)typeMask)
                    << "\n");
  LLVM_DEBUG(dbgs() << " \tnew base tag/expected pointer tag: 0x"
                    << utohexstr((unsigned)newBaseTag) << "\n");
}
/**
 * Applies RLT to memory
 */
void HWAddressSanitizer::ApplyRLT(IRBuilder<> &IRB, Instruction *AI,
                                  Type *rootType, Value *Tag,
                                  const DataLayout &DL) {

  assert(rootType->isAggregateType() && !rootType->isArrayTy() &&
         "RLT can be applied only to non-array aggregate types");

  llvm::DIType *typeDescriptor =
      nullptr; // lookup IR metadata for DI (Local/Global)

  Value *RootAddrLong = untagPointer(IRB, IRB.CreatePointerCast(AI, IntptrTy));
  Value *PaddingTag = Tag; // TODO: handle padding tags

  std::deque<std::tuple<Type *, uint8_t, uint8_t, uint8_t, size_t>> AggQueue;

  auto rootTypeMemberOffsets =
      DL.getStructLayout(cast<StructType>(rootType))->getMemberOffsets();

  uint8_t fatherT = 0;
  uint8_t fatherL = 0;
  uint8_t sonIdx = 1; // NOTE: indexes start at 1

  for (auto subtype : rootType->subtypes()) {
    AggQueue.push_back(std::make_tuple(subtype, fatherT, fatherL, sonIdx,
                                       rootTypeMemberOffsets[sonIdx - 1]));
    sonIdx++;
  } // init for

  while (!AggQueue.empty()) {

    /**
     * UNIONs
     *  1 - layout seems to be inferred by the compiler -> maybe based on
     * first use? 2 - size seems to be 0 when called upon the union itself 3 -
     * in presence of padding in the union, compiler assumes it an i8 array
     * FLEX MEMBERS 1 - their size is 0 --> just don't tag them
     * INSTRUMENTATION 1 - I suspect compiler will still optimize away tag
     * stores 2 - does it have to be so horribly inefficient?
     */

    auto el_pair = AggQueue.front();
    AggQueue.pop_front();

    Type *sonType = std::get<0>(el_pair); // GEP

    // my father's tag
    fatherT = std::get<1>(el_pair); // from top-byte

    // level of nesting wrt to the top aggregate
    fatherL = std::get<2>(el_pair); // GEP

    // index of the (sub) field in the (sub)type
    sonIdx = std::get<3>(el_pair); // GEPs provide you with this info

    // offset of the field from the beginning of the aggregate in memory
    size_t sonOffset = std::get<4>(el_pair); // current offset from the root ptr

    if (sonType->isAggregateType() &&
        !sonType->isArrayTy()) { /*either struct or union */
      // TAG memory associated to nested aggregate type
      // TODO: should sonIdx be %'ed???
      uint8_t sonT =
          (fatherT + sonIdx) % 16; // tag of ptr to this field, expected tag

      uint8_t sonMask = sonType->getNumContainedTypes() % 16u;
      auto rotatedMask = rotateOn4bits(sonMask, sonIdx);
      auto newBaseTag = (rotatedMask ^ sonT);
      // fields tags will be newBaseTag + field index

      debugAggregateVisit(sonType, fatherL, sonT, sonMask, newBaseTag);

      uint8_t count = 0;
      auto sonSubfieldsCount = sonType->getNumContainedTypes();

      auto sonSubfieldsOffsets =
          DL.getStructLayout(cast<StructType>(sonType))->getMemberOffsets();
      size_t currSonSubfieldOffset = 0;

      for (Type *subtype : llvm::reverse(sonType->subtypes())) {
        currSonSubfieldOffset =
            sonSubfieldsOffsets[sonSubfieldsCount - count - 1] + sonOffset;
        AggQueue.push_front(
            std::make_tuple(subtype, newBaseTag, (fatherL + 1) % 8,
                            sonSubfieldsCount - count, currSonSubfieldOffset));
        count++;
      } // visits the elements of the sonType if this is an aggregate and
        // establishes tags

    } else {
      /*Visit memory location and tag it */
      assert(sonType->isSized() && "Type must be sized"); // CHECK
      uint8_t sonT = (fatherT + sonIdx) % 16;
      uint8_t sonTag = sonT | (fatherL << 4);
      assert((sonT & 0x80) == 0 &&
             "ROOT POINTER BIT must be set to 0 in memory tags");

      IRB.CreateCall(
          HwasanTagMemoryFunc,
          {IRB.CreateIntToPtr(
               IRB.CreateAdd(IRB.CreatePtrToInt(RootAddrLong, IntptrTy),
                             ConstantInt::get(IntptrTy, sonOffset)),
               PtrTy),
           ConstantInt::get(Int8Ty, sonTag),
           ConstantInt::get(IntptrTy, DL.getTypeAllocSize(sonType)),
           ConstantInt::get(
               IntptrTy, typeDescriptor
                             ? typeDescriptor->getLine()
                             : 0)}); // NOTE: this is a bogus parameter for now
      LLVM_DEBUG(dbgs() << " [++] TAG MEM @ offset " << sonOffset << " -> 0x"
                        << utohexstr((unsigned)sonTag) << "\n");
    } // else ->visit memory location
  } // while agg queue not empty
} // ApplyRLT

void debugTagAlloca(AllocaInst *AI, size_t Size, size_t AlignedSize,
                    size_t scale, Value *Tag) {
  LLVM_DEBUG(dbgs() << " [++] tagAlloca: not instrumenting with calls\n");
  // shadowSize = size
  LLVM_DEBUG(dbgs() << " [++] Aligned size : " << AlignedSize << "\n");
  LLVM_DEBUG(dbgs() << " [++] Size : " << Size << "\n");
  LLVM_DEBUG(dbgs() << " [++] Mapping scale : " << scale << "\n");
  LLVM_DEBUG(dbgs() << " [++]   Tag value : ");
  LLVM_DEBUG(Tag->print(dbgs()));
  LLVM_DEBUG(dbgs() << "\n");
  AI->getAllocatedType()->print(dbgs());
  LLVM_DEBUG(dbgs() << "\n");
  LLVM_DEBUG(dbgs() << " [++] Num contained types : "
                    << AI->getAllocatedType()->getNumContainedTypes());
  LLVM_DEBUG(dbgs() << "\n");
  // print contained types
  for (Type *contType : AI->getAllocatedType()->subtypes()) {
    LLVM_DEBUG(dbgs() << " \t[++] Contained type: ");
    LLVM_DEBUG(contType->print(dbgs()));
    LLVM_DEBUG(dbgs() << "\n");
  }
  LLVM_DEBUG(dbgs() << "\n");
}

void pokeIntoAggregate(Type *sonType, unsigned currNestingLevel,
                       uint8_t expectedTag, uint8_t typeMask,
                       uint8_t newBaseTag, size_t numElementsInSubtype) {
  LLVM_DEBUG(dbgs() << " [++] POKING INTO AGGREGATE: ");
  LLVM_DEBUG(dbgs() << sonType->getStructName());
  LLVM_DEBUG(dbgs() << " at nesting level: " << (unsigned)currNestingLevel
                    << "\n");
  LLVM_DEBUG(dbgs() << " \texpected tag: 0x" << utohexstr((unsigned)expectedTag)
                    << "\n");
  LLVM_DEBUG(dbgs() << " \ttype mask: 0x" << utohexstr((unsigned)typeMask)
                    << "\n");
  LLVM_DEBUG(dbgs() << " \tnew base tag: 0x" << utohexstr((unsigned)newBaseTag)
                    << "\n");
  LLVM_DEBUG(dbgs() << " \tnumber of elements in subtype: "
                    << numElementsInSubtype << "\n");
  LLVM_DEBUG(dbgs() << "\n");
}

void HWAddressSanitizer::tagAlloca(IRBuilder<> &IRB, AllocaInst *AI, Value *Tag,
                                   size_t Size, const DataLayout &DL) {
  size_t AlignedSize = alignTo(Size, Mapping.getObjectAlignment());
  if (!UseShortGranules)
    Size = AlignedSize;
  debugTagAlloca(AI, Size, AlignedSize, Mapping.scale(), Tag);

  Tag = IRB.CreateTrunc(Tag, Int8Ty);
  // if (InstrumentWithCalls) {
  //   LLVM_DEBUG(dbgs() << " [++] tagAlloca: instrumenting with calls\n");
  //   IRB.CreateCall(HwasanTagMemoryFunc,
  //                  {IRB.CreatePointerCast(AI, PtrTy), Tag,
  //                   ConstantInt::get(IntptrTy, AlignedSize)});
  // } else {
  ApplyRLT(IRB, AI, AI->getAllocatedType(), Tag, DL);
  // } // if not instrumenting with calls
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

Value *HWAddressSanitizer::getStackBaseTag(IRBuilder<> &IRB) {
  if (ClGenerateTagsWithCalls)
    return nullptr;
  if (StackBaseTag)
    return StackBaseTag;
  // Extract some entropy from the stack pointer for the tags.
  // Take bits 20..28 (ASLR entropy) and xor with bits 0..8 (these differ
  // between functions).
  Value *FramePointerLong = getCachedFP(IRB);
  Value *StackTag =
      applyTagMask(IRB, IRB.CreateXor(FramePointerLong,
                                      IRB.CreateLShr(FramePointerLong, 20)));
  StackTag->setName("hwasan.stack.base.tag");
  return StackTag;
}

Value *HWAddressSanitizer::getAllocaTag(IRBuilder<> &IRB, Value *StackTag,
                                        unsigned AllocaNo) {
  if (ClGenerateTagsWithCalls)
    return getNextTagWithCall(IRB);
  return IRB.CreateXor(
      StackTag, ConstantInt::get(StackTag->getType(), retagMask(AllocaNo)));
}

Value *HWAddressSanitizer::getUARTag(IRBuilder<> &IRB) {
  Value *FramePointerLong = getCachedFP(IRB);
  Value *UARTag =
      applyTagMask(IRB, IRB.CreateLShr(FramePointerLong, PointerTagShift));

  UARTag->setName("hwasan.uar.tag");
  return UARTag;
}

// Add a tag to an address.
Value *HWAddressSanitizer::tagPointer(IRBuilder<> &IRB, Type *Ty,
                                      Value *PtrLong, Value *Tag) {
  assert(!UsePageAliases);
  Value *TaggedPtrLong;
  if (CompileKernel) {
    // Kernel addresses have 0xFF in the most significant byte.
    Value *ShiftedTag =
        IRB.CreateOr(IRB.CreateShl(Tag, PointerTagShift),
                     ConstantInt::get(IntptrTy, (1ULL << PointerTagShift) - 1));
    TaggedPtrLong = IRB.CreateAnd(PtrLong, ShiftedTag);
  } else {
    // Userspace can simply do OR (tag << PointerTagShift);
    Value *ShiftedTag = IRB.CreateShl(Tag, PointerTagShift);
    TaggedPtrLong = IRB.CreateOr(PtrLong, ShiftedTag);
  }
  return IRB.CreateIntToPtr(TaggedPtrLong, Ty);
}

// Remove tag from an address.
inline Value *HWAddressSanitizer::untagPointer(IRBuilder<> &IRB,
                                               Value *PtrLong) {
  assert(!UsePageAliases);
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

void HWAddressSanitizer::emitPrologue(IRBuilder<> &IRB, bool WithFrameRecord) {
  if (!Mapping.isInTls())
    ShadowBase = getShadowNonTls(IRB);
  else if (!WithFrameRecord && TargetTriple.isAndroid())
    ShadowBase = getDynamicShadowIfunc(IRB);

  if (!WithFrameRecord && ShadowBase)
    return;

  Value *SlotPtr = nullptr;
  Value *ThreadLong = nullptr;
  Value *ThreadLongMaybeUntagged = nullptr;

  auto getThreadLongMaybeUntagged = [&]() {
    if (!SlotPtr)
      SlotPtr = getHwasanThreadSlotPtr(IRB);
    if (!ThreadLong)
      ThreadLong = IRB.CreateLoad(IntptrTy, SlotPtr);
    // Extract the address field from ThreadLong. Unnecessary on AArch64 with
    // TBI.
    return TargetTriple.isAArch64() ? ThreadLong
                                    : untagPointer(IRB, ThreadLong);
  };

  if (WithFrameRecord) {
    switch (ClRecordStackHistory) {
    case libcall: {
      // Emit a runtime call into hwasan rather than emitting instructions for
      // recording stack history.
      Value *FrameRecordInfo = getFrameRecordInfo(IRB);
      IRB.CreateCall(HwasanRecordFrameRecordFunc, {FrameRecordInfo});
      break;
    }
    case instr: {
      ThreadLongMaybeUntagged = getThreadLongMaybeUntagged();

      StackBaseTag = IRB.CreateAShr(ThreadLong, 3);

      // Store data to ring buffer.
      Value *FrameRecordInfo = getFrameRecordInfo(IRB);
      Value *RecordPtr =
          IRB.CreateIntToPtr(ThreadLongMaybeUntagged, IRB.getPtrTy(0));
      IRB.CreateStore(FrameRecordInfo, RecordPtr);

      IRB.CreateStore(memtag::incrementThreadLong(IRB, ThreadLong, 8), SlotPtr);
      break;
    }
    case none: {
      llvm_unreachable(
          "A stack history recording mode should've been selected.");
    }
    }
  }

  if (!ShadowBase) {
    if (!ThreadLongMaybeUntagged)
      ThreadLongMaybeUntagged = getThreadLongMaybeUntagged();

    // Get shadow base address by aligning RecordPtr up.
    // Note: this is not correct if the pointer is already aligned.
    // Runtime library will make sure this never happens.
    ShadowBase = IRB.CreateAdd(
        IRB.CreateOr(
            ThreadLongMaybeUntagged,
            ConstantInt::get(IntptrTy, (1ULL << kShadowBaseAlignment) - 1)),
        ConstantInt::get(IntptrTy, 1), "hwasan.shadow");
    ShadowBase = IRB.CreateIntToPtr(ShadowBase, PtrTy);
  }
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

bool HWAddressSanitizer::instrumentStack(
    memtag::StackInfo &SInfo, Value *StackTag, const DominatorTree &DT,
    const PostDominatorTree &PDT, const LoopInfo &LI, const DataLayout &DL) {
  // Ideally, we want to calculate tagged stack base pointer, and rewrite all
  // alloca addresses using that. Unfortunately, offsets are not known yet
  // (unless we use ASan-style mega-alloca). Instead we keep the base tag in a
  // temp, shift-OR it into each alloca address and xor with the retag mask.
  // This generates one extra instruction per alloca use.
  unsigned int I = 0;

  for (auto &KV : SInfo.AllocasToInstrument) {
    errs() << "Instrumenting alloca: " << *(KV.first)
           << "\n"; // show me the instruction
    auto N = I++;
    auto *AI = KV.first;
    memtag::AllocaInfo &Info = KV.second;
    IRBuilder<> IRB(AI->getNextNonDebugInstruction());

    // Replace uses of the alloca with tagged address.
    Value *Tag = getAllocaTagRootPtr(IRB, StackTag, N);
    Value *AILong = IRB.CreatePointerCast(AI, IntptrTy);
    Value *AINoTagLong = untagPointer(IRB, AILong);
    Value *Replacement = tagPointer(IRB, AI->getType(), AINoTagLong, Tag);
    std::string Name =
        AI->hasName() ? AI->getName().str() : "alloca." + itostr(N);
    Replacement->setName(Name + ".hwasan"); // interesting

    size_t Size = memtag::getAllocaSizeInBytes(*AI);
    size_t AlignedSize =
        alignTo(Size, Mapping.getObjectAlignment()); // WATCH OUT
    errs() << "Alloca size: " << Size << ", aligned size: " << AlignedSize
           << "\n"; // show me the size
    Value *AICast = IRB.CreatePointerCast(AI, PtrTy);

    auto HandleLifetime = [&](IntrinsicInst *II) {
      // Set the lifetime intrinsic to cover the whole alloca. This reduces
      // the set of assumptions we need to make about the lifetime. Without
      // this we would need to ensure that we can track the lifetime pointer
      // to a constant offset from the alloca, and would still need to change
      // the size to include the extra alignment we use for the untagging to
      // make the size consistent.
      //
      // The check for standard lifetime below makes sure that we have exactly
      // one set of start / end in any execution (i.e. the ends are not
      // reachable from each other), so this will not cause any problems.
      II->setArgOperand(0, ConstantInt::get(Int64Ty, AlignedSize));
      II->setArgOperand(1, AICast);
    };
    llvm::for_each(Info.LifetimeStart, HandleLifetime);
    llvm::for_each(Info.LifetimeEnd, HandleLifetime);

    AI->replaceUsesWithIf(Replacement, [AICast, AILong](const Use &U) {
      auto *User = U.getUser();
      return User != AILong && User != AICast && !isa<LifetimeIntrinsic>(User);
    });

    memtag::annotateDebugRecords(Info, retagMask(N));

    // auto TagEnd = [&](Instruction *Node) {
    //   IRB.SetInsertPoint(Node);
    //   // When untagging, use the `AlignedSize` because we need to set the
    //   tags
    //   // for the entire alloca to original. If we used `Size` here, we
    //   would
    //   // keep the last granule tagged, and store zero in the last byte of
    //   the
    //   // last granule, due to how short granules are implemented.
    //   tagAlloca(IRB, AI, UARTag, AlignedSize, DL);
    // };
    // Calls to functions that may return twice (e.g. setjmp) confuse the
    // postdominator analysis, and will leave us to keep memory tagged after
    // function return. Work around this by always untagging at every return
    // statement if return_twice functions are called.
    // bool StandardLifetime =
    //     !SInfo.CallsReturnTwice && SInfo.UnrecognizedLifetimes.empty() &&
    //     memtag::isStandardLifetime(Info.LifetimeStart, Info.LifetimeEnd,
    //     &DT,
    //                                &LI, ClMaxLifetimes);
    // assert(!DetectUseAfterScope &&
    //        "FieldArmor does not support UAS"); // GET RID OF UAS

    // if (DetectUseAfterScope && StandardLifetime) {
    //   IntrinsicInst *Start = Info.LifetimeStart[0];
    //   IRB.SetInsertPoint(Start->getNextNode());
    //   tagAlloca(IRB, AI, Tag, Size, DL);
    //   if (!memtag::forAllReachableExits(DT, PDT, LI, Start,
    //   Info.LifetimeEnd,
    //                                     SInfo.RetVec, TagEnd)) {
    //     for (auto *End : Info.LifetimeEnd)
    //       End->eraseFromParent();
    //   }
    // } else {
    tagAlloca(IRB, AI, Tag, Size, DL);
    // for (auto *RI : SInfo.RetVec)
    //   TagEnd(RI);// I DONT WANT THIS PORCODIO
    // We inserted tagging outside of the lifetimes, so we have to remove
    // them.
    for (auto &II : Info.LifetimeStart)
      II->eraseFromParent();
    for (auto &II : Info.LifetimeEnd)
      II->eraseFromParent();
    // }
    memtag::alignAndPadAlloca(Info, Mapping.getObjectAlignment());
  }
  for (auto &I : SInfo.UnrecognizedLifetimes)
    I->eraseFromParent();
  return true;
}

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

  auto SkipRandom = [&]() {
    if (!ClRandomKeepRate.getNumOccurrences())
      return false;
    std::bernoulli_distribution D(ClRandomKeepRate);
    return !D(*Rng);
  };

  bool Skip = SkipRandom() || SkipHot();
  emitRemark(F, FAM.getResult<OptimizationRemarkEmitterAnalysis>(F), Skip);
  return Skip;
}

void HWAddressSanitizer::sanitizeFunction(Function &F,
                                          FunctionAnalysisManager &FAM) {
  if (&F == HwasanCtorFunction)
    return;

  // Do not apply any instrumentation for naked functions.
  if (F.hasFnAttribute(Attribute::Naked))
    return;

  if (!F.hasFnAttribute(Attribute::SanitizeHWAddress))
    return;

  if (F.empty())
    return;

  NumTotalFuncs++;

  OptimizationRemarkEmitter &ORE =
      FAM.getResult<OptimizationRemarkEmitterAnalysis>(F);

  if (selectiveInstrumentationShouldSkip(F, FAM))
    return;

  NumInstrumentedFuncs++;

  SmallVector<InterestingMemoryOperand, 16> OperandsToInstrument;
  SmallVector<MemIntrinsic *, 16> IntrinToInstrument;
  SmallVector<Instruction *, 8> LandingPadVec;
  SmallVector<GetElementPtrInst *, 40> GEPsToInstrument;

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
      if (!ignoreMemIntrinsic(ORE, MI))
        IntrinToInstrument.push_back(MI);

    if (GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(&Inst)) {
      GEPsToInstrument.push_back(GEPI);
    }

    if (auto *CB = dyn_cast<CallBase>(&Inst)) {

      if (CB->getCalledFunction() &&
          CB->getCalledFunction()->getName().contains(
              "alloc")) { // TODO: how to distinguish libc malloc from
                          // wrappers?
        LLVM_DEBUG(dbgs() << " Found call to memory allocation function: "
                          << *CB << "\n");
      }
    }

  } // instrument stack to build lifetime info, find memset/memcpy calls, get
    // info on how to instrument for exception handling (landing pads)
  // Dump interesting memory operands iterating over InterestingMemoryOperand
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
  emitPrologue(EntryIRB,
               /*WithFrameRecord*/ ClRecordStackHistory != none &&
                   Mapping.withFrameRecord() &&
                   !SInfo.AllocasToInstrument.empty());

  if (!SInfo.AllocasToInstrument.empty()) {
    const DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);
    const PostDominatorTree &PDT = FAM.getResult<PostDominatorTreeAnalysis>(F);
    const LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
    Value *StackTag = getStackBaseTag(EntryIRB);
    instrumentStack(SInfo, StackTag, DT, PDT, LI, F.getDataLayout());
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

  DominatorTree *DT = FAM.getCachedResult<DominatorTreeAnalysis>(F);
  PostDominatorTree *PDT = FAM.getCachedResult<PostDominatorTreeAnalysis>(F);
  LoopInfo *LI = FAM.getCachedResult<LoopAnalysis>(F);
  DomTreeUpdater DTU(DT, PDT, DomTreeUpdater::UpdateStrategy::Lazy);
  const DataLayout &DL = F.getDataLayout();
  for (auto &Operand : OperandsToInstrument)
    instrumentMemAccess(Operand, DTU, LI, DL);
  DTU.flush();

  if (ClInstrumentMemIntrinsics && !IntrinToInstrument.empty()) {
    for (auto *Inst : IntrinToInstrument)
      instrumentMemIntrinsic(Inst);
  }

  LLVM_DEBUG(dbgs() << " [++] FUNCTION " << F.getName()
                    << " -> Total GEPs to instrument: "
                    << GEPsToInstrument.size() << "\n");
  for (auto &GEPI : GEPsToInstrument) {
    InstrumentGEP(GEPI);
    // LLVM_DEBUG(dbgs() << " Instrumented GEP: " << *GEPI << "\n");
  }
  ShadowBase = nullptr;
  StackBaseTag = nullptr;
  CachedFP = nullptr;
}

void dumpGEPDebug(GetElementPtrInst *GEPI) {
  LLVM_DEBUG(dbgs() << " _______________________________\n");
  LLVM_DEBUG(dbgs() << " GEP INSTRUCTION: ");
  LLVM_DEBUG(GEPI->print(dbgs()));
  LLVM_DEBUG(dbgs() << "\n");

  LLVM_DEBUG(dbgs() << "\t SRC TYPE: ");
  LLVM_DEBUG(GEPI->getSourceElementType()->print(dbgs()));
  LLVM_DEBUG(dbgs() << "\n");

  LLVM_DEBUG(dbgs() << "\t DST TYPE: ");
  auto res_type = GEPI->getResultElementType();
  LLVM_DEBUG(res_type->print(dbgs()));
  LLVM_DEBUG(dbgs() << "\n");
  for (auto *User : GEPI->users()) {
    LLVM_DEBUG(dbgs() << "\t\t GEP USER: ");
    LLVM_DEBUG(User->print(dbgs()));
    LLVM_DEBUG(dbgs() << "\n");
  }

  LLVM_DEBUG(dbgs() << "\n _______________________________\n");
}

void dumpGEPUsersWhenRetStruct(GetElementPtrInst *GEPI) {
  auto res_type = GEPI->getResultElementType();
  if (res_type->isStructTy()) {
    StructType *ST = dyn_cast<StructType>(res_type);
    for (auto *User : GEPI->users()) {
      if (ST->getName().starts_with("union")) {
        IRBuilder<> IRB(User->getContext());
        IRB.SetInsertPoint(cast<Instruction>(User)->getNextNode());
        LLVM_DEBUG(dbgs() << "  instrumenting GEP user (union struct): ");
        LLVM_DEBUG(User->print(dbgs()));
        LLVM_DEBUG(dbgs() << "\n");
      }
    }
  }
}

#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Instructions.h"

StringRef getStructODRIdentifier(Instruction *Instr) {
  auto *GEP = dyn_cast<GetElementPtrInst>(Instr);
  if (!GEP)
    return "";

  Type *StructType = GEP->getSourceElementType();
  if (!StructType->isStructTy())
    return "";

  // Get debug location
  auto DbgLoc = GEP->getDebugLoc();
  if (!DbgLoc)
    return "";

  // Get the scope from the debug location
  DIScope *Scope = DbgLoc->getScope();
  if (!Scope)
    return "";

  // Traverse to DILocalScope if possible
  DILocalScope *LocalScope = dyn_cast<DILocalScope>(Scope);
  if (!LocalScope)
    return "";

  // Get the subprogram from the local scope
  DISubprogram *SP = LocalScope->getSubprogram();
  if (!SP)
    return "";

  // Get the compile unit from the subprogram
  DICompileUnit *CU = SP->getUnit();
  if (!CU)
    return "";

  // Search compile unit's retained types
  for (auto *Type : CU->getRetainedTypes()) {
    if (auto *CompType = dyn_cast<DICompositeType>(Type)) {
      if (CompType->getName() == StructType->getStructName()) {
        if (auto *Identifier = CompType->getRawIdentifier()) {
          return Identifier->getString();
        }
      }
    }
  }

  return "";
}

void HWAddressSanitizer::InstrumentGEP(GetElementPtrInst *GEPI) {
  dumpGEPDebug(GEPI);
  auto nOperands = GEPI->getNumOperands();
  assert(nOperands <= 3); // I expect 3 at most TODO: CHECK ON THIS

  /**
   * NOTE: this does not work, assuming a dbg instruction with the type is there
   * is not reliable.
   */

  // lets look the name up in the DI nodes

  auto fatherType = GEPI->getSourceElementType();
  if (!fatherType->isStructTy()) {
    LLVM_DEBUG(
        dbgs() << " Skipping GEP instrumentation: source type is not struct\n");
    return;
  }

  IRBuilder<> IRB(GEPI->getNextNonDebugInstruction());

  auto sonType = GEPI->getResultElementType();
  // IRB.SetInsertPoint(GEPI->getNextNode()); // NOTE: this does not work
  // since after 1-2 instructions, it wont do anything, not even fail or raise
  // an error cases a) outer root pointer accesses non aggregate b) outer root
  // pointer accesses aggregate (struct/union) c) inner pointer accesses non
  // aggregate d) inner pointer accesses aggregate (struct/union)

  Value *resultLong = IRB.CreatePointerCast(GEPI, IntptrTy);

  auto sonIdx =
      IRB.CreateAdd(IRB.CreateZExtOrTrunc(GEPI->getOperand(2), IntptrTy),
                    ConstantInt::get(IntptrTy, 0x1u)); //+1

  Value *fatherTL = IRB.CreateLShr(
      IRB.CreateAnd(resultLong, ConstantInt::get(IntptrTy, 0x7FL << 56L)),
      PointerTagShift); // UNSET RP

  Value *fatherT = IRB.CreateAnd(fatherTL, ConstantInt::get(IntptrTy, 0x0FLu));

  Value *fatherL =
      IRB.CreateAnd(fatherTL, ConstantInt::get(IntptrTy, 0x70Lu)); /*01110000*/
  // LEVEL is aligned and ready to be applied

  Value *sonTag = nullptr;

  if (!sonType->isStructTy()) {

    Value *sonT = IRB.CreateURem(IRB.CreateAdd(fatherT, sonIdx),
                                 ConstantInt::get(IntptrTy, 0x10Lu));
    sonTag = IRB.CreateOr(sonT, fatherL);
  }

  else {

    Value *mask =
        ConstantInt::get(IntptrTy, sonType->getNumContainedTypes() % 16u);

    Value *positions =
        IRB.CreateURem(sonIdx, ConstantInt::get(IntptrTy, 0x4Lu));

    Value *rotatedMask = IRB.CreateOr(
        IRB.CreateLShr(
            mask, IRB.CreateSub(ConstantInt::get(IntptrTy, 0x4Lu), positions)),
        IRB.CreateShl(mask, positions));
    rotatedMask = IRB.CreateAnd(
        rotatedMask, ConstantInt::get(IntptrTy, 0x0FLu)); // keep lower 4 bits
    Value* expectedSonT = IRB.CreateURem(
        IRB.CreateAdd(fatherT, sonIdx), ConstantInt::get(IntptrTy, 0x10Lu));

    Value *sonT = IRB.CreateXor(rotatedMask, expectedSonT); // DEBUG THIS
    // Value *sonT = IRB.CreateURem(IRB.CreateAdd(maskedFatherT, sonIdx),
    //                              ConstantInt::get(IntptrTy, 0x10Lu));
    
    Value *sonL = IRB.CreateShl(
        IRB.CreateURem(IRB.CreateAdd(IRB.CreateLShr(fatherL, 4u),
                                     ConstantInt::get(IntptrTy, 1u)),
                       ConstantInt::get(IntptrTy, 0x8u)),
        4u); // level aligned and ready to be applied
    sonTag = IRB.CreateOr(IRB.CreateOr(sonT, sonL),
                          ConstantInt::get(IntptrTy, 0x80Lu)); // set RP bit
  }

  Value *untaggedResLong = IRB.CreateAnd(
      resultLong, ConstantInt::get(resultLong->getType(),
                                   ~(TagMaskByte << PointerTagShift)));
  Value *untaggedResLongPtr = IRB.CreatePointerCast(untaggedResLong, IntptrTy);
  Value *taggedPointer =
      tagPointer(IRB, GEPI->getType(), untaggedResLongPtr, sonTag);

  std::string Name = GEPI->hasName() ? GEPI->getName().str()
                                     : "gep." + itostr(++instrumentedGEPs);
  taggedPointer->setName(Name + ".fieldarmor");
  Value *indexOfTaggedPointer = sonIdx;
  indexOfTaggedPointer->setName(Name + ".fieldarmor.idx");

  Value *GEPICastToPtr = IRB.CreatePointerCast(GEPI, PtrTy); //?? TODO REMOVE

  GEPI->replaceUsesWithIf(
      taggedPointer, [GEPICastToPtr, resultLong](const Use &U) {
        auto *User = U.getUser();
        return User != resultLong && User != GEPICastToPtr &&
               !isa<LifetimeIntrinsic>(User); // NOOOO
      });
}

void HWAddressSanitizer::instrumentGlobalAggregate(GlobalVariable *GV,
                                                   uint8_t Tag,
                                                   const DataLayout &DL) {
  /** You can assume the GV is an aggregate. Apply RLT schema for the global
   */
  LLVM_DEBUG(dbgs() << " [++] Simulating instrumentation of global aggregate: "
                    << GV->getName() << "\n");
  Constant *Initializer = GV->getInitializer();
  Type *type = Initializer->getType();
  assert(type->isAggregateType());
  LLVM_DEBUG(dbgs() << "\t\tGlobal is struct type ");
  LLVM_DEBUG(type->print(dbgs()));
  LLVM_DEBUG(dbgs() << "\n");
  // create GlobalVar with the associated tag sequence bytes inside so that
  // runtime can use it for tagging sequentially the allocated global method
  // start
  // std::deque<std::tuple<Type *, uint8_t, uint8_t, uint8_t, size_t>>
  // AggQueue;

  // Type *rootType =
  //     GV->getInitializer()->getType(); // the type of the global variable
  // assert(rootType->isAggregateType() &&
  //        "Global variable must be aggregate type");
  // assert(rootType->isSized() && "Global variable must be sized type");
  // std::vector<uint8_t> TagsVector;
  // auto rootTypeMemberOffsets =
  //     DL.getStructLayout(cast<StructType>(rootType))->getMemberOffsets();
  // uint8_t baseTag = 1;
  // uint8_t baseLevelOfNesting = 0;
  // uint8_t idx = 0;
  // for (auto subtype : rootType->subtypes()) {
  //   AggQueue.push_back(std::make_tuple(subtype, baseTag,
  //   baseLevelOfNesting,
  //                                      idx, rootTypeMemberOffsets[idx]));
  //   idx++;
  // }

  // while (!AggQueue.empty()) {
  //   auto el_pair = AggQueue.front();
  //   AggQueue.pop_front();

  //   Type *sonType = std::get<0>(el_pair); // GEP

  //   // my father's tag
  //   uint8_t baseTag = std::get<1>(el_pair); // from top-byte

  //   // level of nesting wrt to the top aggregate
  //   uint8_t currNestingLevel = std::get<2>(el_pair); // GEP

  //   // index of the (sub) field in the (sub)type
  //   uint8_t sonTypeIndex =
  //       std::get<3>(el_pair); // GEPs provide you with this info

  //   // offset of the field from the beginning of the aggregate in memory
  //   size_t currOffset =
  //       std::get<4>(el_pair); // current offset from the root ptr

  //   if (sonType->isAggregateType() &&
  //       !sonType->isArrayTy()) { /*either struct or union */
  //     uint8_t typeMask = sonType->getNumContainedTypes() % 256;
  //     uint8_t expectedTag =
  //         baseTag + sonTypeIndex; // What it means: I expected this to be
  //         the
  //                                  // tag, turns out it is an aggregate ->
  //                                  hence
  //                                  // I'm computing tags for its subfields
  //     auto newBaseTag = (typeMask << 1 ^ expectedTag); // DRAFT
  //     uint8_t count = 0;
  //     auto numElementsInSubtype = sonType->getNumContainedTypes();
  //     // pokeIntoAggregate(sonType, currNestingLevel, expectedTag,
  //     typeMask,
  //     //                   newBaseTag, numElementsInSubtype);
  //     auto memberOffsets =
  //         DL.getStructLayout(cast<StructType>(sonType))->getMemberOffsets();

  //     size_t currSubtypeOffset = 0;

  //     for (Type *subtype : llvm::reverse(sonType->subtypes())) {
  //       currSubtypeOffset =
  //           memberOffsets[numElementsInSubtype - count - 1] + currOffset;
  //       AggQueue.push_front(std::make_tuple(
  //           subtype, newBaseTag, currNestingLevel + 1,
  //           numElementsInSubtype - count - 1, currSubtypeOffset));
  //       count++;
  //     } // visits the elements of the sonType if this is an aggregate and
  //       // establishes tags
  //   } else {

  //     uint8_t newTag = baseTag + sonTypeIndex;
  //     LLVM_DEBUG(dbgs() << "\t\t At offset: " << currOffset
  //                       << " of global, setting tag: " << unsigned(newTag)
  //                       << " for type: ");
  //     LLVM_DEBUG(sonType->print(dbgs()));
  //     LLVM_DEBUG(dbgs() << "\n");
  //     // push in the tagsVector as many bytes equal to tag, as the size of
  //     the
  //     // current type in bytes
  //     uint64_t TypeSizeInBytes = DL.getTypeAllocSize(sonType);
  //     for (uint64_t i = 0; i < TypeSizeInBytes; i++) {
  //       TagsVector.push_back(newTag);
  //     }
  //   } // done collecting tags

  //     // method end
  //     // create new global variable with a fixed size byte array inside
  //     holding
  //     // the tags -> constant
  //     uint64_t TagSize =
  //     alignTo(M.getDataLayout().getTypeAllocSize(rootType),
  //                                Mapping.getObjectAlignment());

  //     Value *Init = ConstantAggregateZero::get(ArrayType::get(Int8Ty,
  //     TagSize));

  //     for (auto tag : TagsVector) {
  //       Init = ConstantExpr::getInsertValue(Init, ConstantInt::get(Int8Ty,
  //       tag),
  //                                           {0,
  //                                           (int64_t)TagsVector.size()});
  //     }

  //     auto *NewGV = new GlobalVariable(M, Init->getType(), true,
  //                                      GlobalValue::ExternalLinkage, Init,
  //                                      GV->getName() + ".hwasan.tags");
  //     NewGV->copyAttributesFrom(GV);
  //     NewGV->setLinkage(GlobalValue::PrivateLinkage);
  //     NewGV->copyMetadata(GV, 0);
  //     NewGV->setAlignment(
  //         std::max(GV->getAlign().valueOrOne(),
  //         Mapping.getObjectAlignment()));

  //     NewGV->setUnnamedAddr(GlobalValue::UnnamedAddr::None);

  //     // Descriptor format (assuming little-endian):
  //     // bytes 0-3: relative address of global
  //     // bytes 4-6: size of global (16MB ought to be enough for anyone, but
  //     in
  //     // case it isn't, we create multiple descriptors) byte 7: tag
  //     auto *DescriptorTy = StructType::get(Int32Ty, Int32Ty);
  //     auto SizeInBytes = TagsVector.size(); // TODO: check

  //     const uint64_t MaxDescriptorSize = 0xfffff0;
  //     for (uint64_t DescriptorPos = 0; DescriptorPos < SizeInBytes;
  //          DescriptorPos += MaxDescriptorSize) {
  //       auto *Descriptor = new GlobalVariable(
  //           M, DescriptorTy, true, GlobalValue::PrivateLinkage, nullptr,
  //           GV->getName() + ".hwasan.tags.descriptor");
  //       auto *GVRelPtr = ConstantExpr::getTrunc(
  //           ConstantExpr::getAdd(
  //               ConstantExpr::getSub(
  //                   ConstantExpr::getPtrToInt(NewGV, Int64Ty),
  //                   ConstantExpr::getPtrToInt(Descriptor, Int64Ty)),
  //               ConstantInt::get(Int64Ty, DescriptorPos)),
  //           Int32Ty);
  //       uint32_t Size =
  //           std::min(SizeInBytes - DescriptorPos, MaxDescriptorSize);
  //       auto *SizeAndTag =
  //           ConstantInt::get(Int32Ty, Size | (uint32_t(Tag) << 24)); //
  //           review this later
  //       Descriptor->setComdat(NewGV->getComdat());
  //       Descriptor->setInitializer(
  //           ConstantStruct::getAnon({GVRelPtr, SizeAndTag}));
  //       Descriptor->setSection("hwasan_globals");
  //       Descriptor->setMetadata(LLVMContext::MD_associated,
  //                               MDNode::get(*C,
  //                               ValueAsMetadata::get(NewGV)));
  //       appendToCompilerUsed(M, Descriptor);
  //     }
}

void HWAddressSanitizer::instrumentGlobal(GlobalVariable *GV, uint8_t Tag) {
  assert(!UsePageAliases);
  /** This method is called for all globals, ideally we want to filter on
   * aggregates */

  Constant *Initializer = GV->getInitializer();
  Type *type = Initializer->getType();
  LLVM_DEBUG(dbgs() << " [++] Instrumenting global: " << GV->getName() << "\n");

  if (type->isAggregateType() && !type->isArrayTy()) {
    LLVM_DEBUG(dbgs() << "  Global is struct type ");
    LLVM_DEBUG(type->print(dbgs()));
    LLVM_DEBUG(dbgs() << "\n");
  }

  uint64_t SizeInBytes =
      M.getDataLayout().getTypeAllocSize(Initializer->getType());
  uint64_t NewSize = alignTo(
      SizeInBytes,
      Mapping.getObjectAlignment()); // this might no longer be necessary
  if (SizeInBytes != NewSize) {
    LLVM_DEBUG(dbgs() << "  Global size " << SizeInBytes
                      << " is not multiple of alignment , padding with "
                         "zeros and tag byte\n");
    // Pad the initializer out to the next multiple of 16 bytes and add the
    // required short granule tag.
    std::vector<uint8_t> Init(NewSize - SizeInBytes, 0);
    Init.back() = Tag;
    Constant *Padding = ConstantDataArray::get(*C, Init);
    Initializer = ConstantStruct::getAnon({Initializer, Padding});
  }

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

  // Descriptor format (assuming little-endian):
  // bytes 0-3: relative address of global
  // bytes 4-6: size of global (16MB ought to be enough for anyone, but in
  // case it isn't, we create multiple descriptors) byte 7: tag
  auto *DescriptorTy = StructType::get(Int32Ty, Int32Ty);
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
            ConstantInt::get(Int64Ty, DescriptorPos)),
        Int32Ty);
    uint32_t Size = std::min(SizeInBytes - DescriptorPos, MaxDescriptorSize);
    auto *SizeAndTag = ConstantInt::get(Int32Ty, Size | (uint32_t(Tag) << 24));
    Descriptor->setComdat(NewGV->getComdat());
    Descriptor->setInitializer(ConstantStruct::getAnon({GVRelPtr, SizeAndTag}));
    Descriptor->setSection("hwasan_globals");
    Descriptor->setMetadata(LLVMContext::MD_associated,
                            MDNode::get(*C, ValueAsMetadata::get(NewGV)));
    appendToCompilerUsed(M, Descriptor);
  }

  Constant *Aliasee = ConstantExpr::getIntToPtr(
      ConstantExpr::getAdd(
          ConstantExpr::getPtrToInt(NewGV, Int64Ty),
          ConstantInt::get(Int64Ty, uint64_t(Tag) << PointerTagShift)),
      GV->getType());
  auto *Alias = GlobalAlias::create(GV->getValueType(), GV->getAddressSpace(),
                                    GV->getLinkage(), "", Aliasee, &M);
  Alias->setVisibility(GV->getVisibility());
  Alias->takeName(GV);
  GV->replaceAllUsesWith(Alias);
  GV->eraseFromParent();
}

void HWAddressSanitizer::instrumentGlobals() {
  std::vector<GlobalVariable *> Globals;
  for (GlobalVariable &GV : M.globals()) {
    LLVM_DEBUG(dbgs() << " -> Considering global: " << GV.getName()
                      << " with linkage " << GV.getLinkage()
                      << " and initializer "
                      << (GV.hasInitializer() ? GV.getInitializer()->getName()
                                              : "ciao")
                      << "\n");
    for (auto gv_user : GV.users()) {
      LLVM_DEBUG(dbgs() << "\t   User: ");
      LLVM_DEBUG(gv_user->print(dbgs()));
      LLVM_DEBUG(dbgs() << "\n");
    }

    if (GV.hasSanitizerMetadata() && GV.getSanitizerMetadata().NoHWAddress)
      continue;

    if (GV.isDeclarationForLinker() || GV.getName().starts_with("llvm.") ||
        GV.isThreadLocal())
      continue;

    // Common symbols can't have aliases point to them, so they can't be
    // tagged.
    if (GV.hasCommonLinkage())
      continue;

    // Globals with custom sections may be used in __start_/__stop_
    // enumeration, which would be broken both by adding tags and
    // potentially by the extra padding/alignment that we insert.
    if (GV.hasSection())
      continue;
    if (!GV.getInitializer()->getType()->isStructTy())
      continue; // short circuit this -> only structs/unions
    Globals.push_back(&GV);
  }

  MD5 Hasher;
  Hasher.update(M.getSourceFileName());
  MD5::MD5Result Hash;
  Hasher.final(Hash);
  uint8_t Tag = Hash[0];

  assert(TagMaskByte >= 16);

  for (GlobalVariable *GV : Globals) {
    // Don't allow globals to be tagged with something that looks like a
    // short-granule tag, otherwise we lose inter-granule overflow
    // detection, as the fast path shadow-vs-address check succeeds.
    if (Tag < 16 || Tag > TagMaskByte)
      Tag = 16;
    // instrumentGlobal(GV, Tag++);
    instrumentGlobalAggregate(GV, Tag++, M.getDataLayout());
  }
}

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

  // Tune for the target.
  if (TargetTriple.isOSFuchsia()) {
    // Fuchsia is always PIE, which means that the beginning of the address
    // space is always available.
    SetFixed(0);
  } else if (CompileKernel || InstrumentWithCalls) {
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
  errs() << "HWAddressSanitizer Shadow Mapping: "
         << (Kind == OffsetKind::kFixed ? "fixed" : "dynamic") << " offset, "
         << "scale " << scale() << ", " << kDefaultShadowScale << ", "
         << (WithFrameRecord ? "with" : "without") << " frame record\n";
}

Value *HWAddressSanitizer::getAllocaTagRootPtr(IRBuilder<> &IRB,
                                               Value *StackTag,
                                               unsigned AllocaNo) {
  return ConstantInt::get(StackTag->getType(), 0b10000000);
}