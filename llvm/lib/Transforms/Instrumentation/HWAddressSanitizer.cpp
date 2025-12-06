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

static const size_t kDefaultShadowScale = 0; // 1 to 1 mapping in shadow memory

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
              cl::Hidden, cl::init(false)); // TODO: use for testing later

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

STATISTIC(NumTotalFuncs, "Number of total funcs");
STATISTIC(NumInstrumentedFuncs, "Number of instrumented funcs");
STATISTIC(NumNoProfileSummaryFuncs, "Number of funcs without PS");
STATISTIC(NumLiteralStructs, "Number of literal structs encountered");
STATISTIC(NumInstrumentedGEPs, "Number of instrumented GEP instructions");
STATISTIC(NumInstrumentedGlobals, "Number of instrumented global variables");
STATISTIC(NumDefinedTagVectors, "Number of defined tag vectors");
STATISTIC(NumProtectedUnions, "Number of protected unions");

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
                     const StackSafetyGlobalInfo *SSI)
      : M(M), SSI(SSI) {
    this->Recover = optOr(ClRecover, Recover);
    this->CompileKernel =
        optOr(ClEnableKhwasan, CompileKernel); // TODO: remove later

    initializeModule(); // globals are initialized in here at some point.
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
  void InstrumentGEP(GetElementPtrInst *GEPI);
  void InstrumentConstGEP(ConstantExpr *GEPI, Type *Ty);
  Value *getRPTag(IRBuilder<> &IRB); // FieldArmor
  Value *ApplyRLT(IRBuilder<> &IRB, Instruction *AI, Type *rootType,
                  const DataLayout &DL);   // TODO: refactor remove DL
  unsigned long long instrumentedGEPs = 0; // TODO make atomic

  u_int8_t *computeTags(StructType *t); // FieldArmor
  void createTagVectors();              // FieldArmor
  void createTagVector(StructType *t);  // FieldArmor
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
  const Triple &TargetTriple = M.getTargetTriple();
  if (shouldUseStackSafetyAnalysis(TargetTriple, Options.DisableOptimization))
    SSI = &MAM.getResult<StackSafetyGlobalAnalysis>(M);

  HWAddressSanitizer HWASan(M, Options.CompileKernel, Options.Recover, SSI);
  auto &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

  for (Function &F : M)
    HWASan.sanitizeFunction(F, FAM);
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
  untagPointerOperand(O.getInsn(), Addr); // TODO: check on this

  return true;
}

uint8_t rotateOn4bits(uint8_t val, uint8_t positions) {
  positions = positions % 4;
  LLVM_DEBUG(dbgs() << " [FieldArmor DBG] Rotating value: 0x"
                    << utohexstr((unsigned)val) << " by " << (unsigned)positions
                    << " positions\n");
  val = ((val << positions) | (val >> (4 - positions)));
  val = val & 0x0F;
  LLVM_DEBUG(dbgs() << " [FieldArmor DBG] Rotated value: 0x"
                    << utohexstr((unsigned)val) << "\n");
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
Value *HWAddressSanitizer::ApplyRLT(IRBuilder<> &IRB, Instruction *AI,
                                    Type *rootType, const DataLayout &DL) {

  auto structTy = cast<StructType>(rootType);
  auto tagVector = M.getGlobalVariable(
      structTy->getStructName().str() + ".fieldarmor.tagvec", true);

  if (!tagVector) {
    LLVM_DEBUG(dbgs() << " [FieldArmor] no tags vec for alloca: " << *AI
                      << "\n");

    createTagVector(structTy);
  }
  // TODO: pointer must be untagged. Why is it tagged?
  tagVector = M.getGlobalVariable(
      structTy->getStructName().str() + ".fieldarmor.tagvec", true);
  assert(tagVector && "Tag vector must exist here - tagAlloca");
  FunctionCallee fieldarmor_tag_memory = M.getOrInsertFunction(
      "_ZN8__hwasan21fieldarmor_tag_memoryEPvmm", PtrTy, PtrTy, PtrTy, Int64Ty);
  // IRB.SetInsertPoint(AI->getNextNode()); // what if I ignore this?

  return IRB.CreateCall(
      fieldarmor_tag_memory,
      {IRB.CreatePointerCast(AI, PtrTy),
       IRB.CreatePointerCast(tagVector, PtrTy),
       ConstantInt::get(Int64Ty, DL.getTypeAllocSize(rootType))});

} // ApplyRLT

void HWAddressSanitizer::untagAlloca(IRBuilder<> &IRB, AllocaInst *AI,
                                     const DataLayout &DL) {
  /** Apply tag 0 to the previously tagged memory, immaterially of the type. */
  FunctionCallee fieldarmor_tag_memory = M.getOrInsertFunction(
      "_ZN8__hwasan21fieldarmor_tag_memoryEPvmm", PtrTy, PtrTy, PtrTy, Int64Ty);
  Value *NullTagVector = IRB.CreateIntToPtr(ConstantInt::get(IntptrTy, 0),
                                            PtrTy); // all zeroes tag vector
  IRB.CreateCall(
      fieldarmor_tag_memory,
      {IRB.CreatePointerCast(AI, PtrTy), NullTagVector,
       ConstantInt::get(Int64Ty, DL.getTypeAllocSize(AI->getAllocatedType()))});

} // untagAlloca

void HWAddressSanitizer::tagAlloca(IRBuilder<> &IRB, AllocaInst *AI,
                                   const DataLayout &DL) {
  if (StructType *ST = dyn_cast<StructType>(AI->getAllocatedType())) {
    if (ST->isLiteral() || ST->isOpaque()) {
      LLVM_DEBUG(
          dbgs() << " [FieldArmor] RLT for literal/opaque struct. OPAQUE: "
                 << ST->isOpaque() << " LITERAL: " << ST->isLiteral() << *ST
                 << "\n");
      return;
    } // if literal or opaque -> TODO: fix this shit!!!
    else {
      ApplyRLT(IRB, AI, AI->getAllocatedType(), DL);
      return;
      // safe to apply to struct here}
    }
  }
  if (ArrayType *AT = dyn_cast<ArrayType>(AI->getAllocatedType())) {
    LLVM_DEBUG(dbgs() << " [FieldArmor] tagAlloca ON ARRAY TYPE: " << *AT
                      << "\n");
    auto elementType = AT->getElementType();
    assert(elementType->isStructTy()); // TODO: handle other cases later. But
                                       // this must be true for now!
    // APPROACH 1: for each element, apply RLT. Apply it on a new GEP.
    for (int el = 0; el < AT->getNumElements(); el++) {
      auto *ElementPtr =
          IRB.CreateGEP(elementType, AI, {ConstantInt::get(Int64Ty, el)});
      GetElementPtrInst *GepInstruction = cast<GetElementPtrInst>(ElementPtr);
      ApplyRLT(IRB, GepInstruction, elementType, DL);
      // now replace all the users
    } // for each element, tag
    return;
  }
  assert(false && "This should be unreachable.");
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

    // inspect the type
    if (AllocaInst *AIcast = dyn_cast<AllocaInst>(AI)) {
      Type *allocatedType = AIcast->getAllocatedType();

      if (allocatedType->isArrayTy()) {
        auto elementType = allocatedType->getArrayElementType();
        if (!elementType->isStructTy()) {
          LLVM_DEBUG(dbgs()
                     << " [FieldArmor] Skipping non-struct array alloca: "
                     << *AIcast << "\n");
          continue;
        }
      } // if array, check element type

      else if (!allocatedType->isStructTy()) {

        LLVM_DEBUG(dbgs() << " [FieldArmor] Skipping non-struct alloca: "
                          << *AIcast << "\n");
        continue;
      }
    }
    // Q: is this leaking memory?

    IRBuilder<> IRB(AI->getNextNonDebugInstruction());

    Value *Tag = getRPTag(IRB);
    Value *AILong = IRB.CreatePointerCast(AI, IntptrTy);
    Value *AINoTagLong = untagPointer(IRB, AILong);
    Value *Replacement = tagPointer(IRB, AI->getType(), AINoTagLong, Tag);
    std::string Name =
        AI->hasName() ? AI->getName().str() : "alloca." + itostr(N);
    Replacement->setName(Name + ".hwasan");
    // NOTE: runtime will get the tagged pointer, it untags it, tags memory
    // and then returns it
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

  // if (selectiveInstrumentationShouldSkip(F, FAM))
  //   return; // ALE: DISABLE SELECTIVE INSTRUMENTATION FOR NOW
  // TODO: bring this back later. If it's something hot, theoretically, it
  // should break at some point even without the sanitizer?
  NumInstrumentedFuncs++;

  SmallVector<InterestingMemoryOperand, 16> OperandsToInstrument;
  SmallVector<MemIntrinsic *, 16> IntrinToInstrument;
  SmallVector<Instruction *, 8> LandingPadVec;
  SmallVector<GetElementPtrInst *, 40> GEPsToInstrument;
  SmallVector<ConstantExpr *, 40> ConstGEPsToInstrument;

  const TargetLibraryInfo &TLI = FAM.getResult<TargetLibraryAnalysis>(F);

  memtag::StackInfoBuilder SIB(SSI, DEBUG_TYPE);
  for (auto &Inst : instructions(F)) {

    if (InstrumentStack) {
      SIB.visit(ORE, Inst);
    }

    if (InstrumentLandingPads && isa<LandingPadInst>(Inst))
      LandingPadVec.push_back(&Inst);

    // TODO: filter out something
    getInterestingMemoryOperands(ORE, &Inst, TLI, OperandsToInstrument);

    if (MemIntrinsic *MI = dyn_cast<MemIntrinsic>(&Inst))
      if (!ignoreMemIntrinsic(ORE, MI))
        IntrinToInstrument.push_back(MI);

    if (GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(&Inst)) {
      GEPsToInstrument.push_back(GEPI);
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

  if (!SInfo.AllocasToInstrument.empty()) {
    const DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);
    const PostDominatorTree &PDT = FAM.getResult<PostDominatorTreeAnalysis>(F);
    const LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
    instrumentStack(SInfo, DT, PDT, LI, F.getDataLayout()); // TODO REENABLE
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
  } // Q: what is the value of this?

  DominatorTree *DT = FAM.getCachedResult<DominatorTreeAnalysis>(F);
  PostDominatorTree *PDT = FAM.getCachedResult<PostDominatorTreeAnalysis>(F);
  LoopInfo *LI = FAM.getCachedResult<LoopAnalysis>(F);
  DomTreeUpdater DTU(DT, PDT, DomTreeUpdater::UpdateStrategy::Lazy);
  const DataLayout &DL = F.getDataLayout();
  // for (auto &Operand : OperandsToInstrument)
  //   instrumentMemAccess(Operand, DTU, LI, DL);
  // DTU.flush();

  // if (ClInstrumentMemIntrinsics && !IntrinToInstrument.empty()) {
  //   for (auto *Inst : IntrinToInstrument)
  //     instrumentMemIntrinsic(Inst);
  // }

  // for (auto &GEPI : GEPsToInstrument) {
  //   InstrumentGEP(GEPI);
  // }
  ShadowBase = nullptr;
  // StackBaseTag = nullptr;
  // CachedFP = nullptr;
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

/** Track the origin of this value to check if it has been created/defined
 * from a malloc-like function. I.e., if chunk is dynamically allocated. We do
 * this checking if it is NOT coming from an alloca.*/
// QUESTION: should I do this at LTO?

// // NOTE: I must be able to track back the origin of Base.
// // Recursively traverse back through GEPs to find the original allocation.
// // NOTE: this only works in the current module, if var is defined
// elsewhere, I cannot track it back.

/** FOR LATER: conservatively return FALSE, assuming nothing is dyn alloc.
 * Then, at LTO or so, figure out where the variable comes from. */

// TODO REFACTOR
bool isDynamicallyAllocated(GetElementPtrInst *GEPI,
                            Instruction **endOfTheChain) {
  Value *Base = GEPI->getPointerOperand();

  // 1. If it's a GEP *instruction*, peel nested GEPs.
  while (auto *GEP = dyn_cast<GetElementPtrInst>(Base))
    Base = GEP->getPointerOperand();

  // 2. If it's a GEP *constant expression*, peel its pointer operand.
  if (auto *CE = dyn_cast<ConstantExpr>(Base)) {
    if (CE->getOpcode() == Instruction::GetElementPtr)
      Base = CE->getOperand(0);
  }

  // 3. Strip pointer casts and inbounds constant-offset GEPs.
  Base =
      Base->stripInBoundsConstantOffsets(); // or
                                            // stripPointerCastsAndAliases()
                                            // depending on how aggressive you
                                            // want to be [web:58][web:61]

  // 4. Now check for a global. -> this works
  if (auto *GV = dyn_cast<GlobalVariable>(Base)) {
    LLVM_DEBUG(dbgs() << "GEP source is a global variable: " << GV->getName()
                      << "\n");
    return false; // not dynamically allocated
  }

  if (isa<AllocaInst>(Base)) {
    LLVM_DEBUG(dbgs() << " GEP SOURCE is ALLOCA: " << *Base << "\n");
    return false; // not dynamically allocated -> when would we ever hit this
                  // case?
  }

  else if (isa<CallInst>(Base)) {
    CallInst *CI = cast<CallInst>(Base);
    Function *CalledFunc = CI->getCalledFunction();
    if (CalledFunc) {
      StringRef FuncName = CalledFunc->getName();
      if (FuncName.contains("malloc") || FuncName.contains("calloc") ||
          FuncName.contains("realloc") || FuncName.contains("strdup") ||
          FuncName.contains("memalign") || FuncName.contains("valloc") ||
          FuncName.contains("posix_memalign")) {
        LLVM_DEBUG(dbgs() << " GEP source comes from malloc-like function: "
                          << FuncName << "\n");
        *endOfTheChain = CI;
        return true; // Found a malloc-like function
      }
    } else
      return true; // TODO: review this

  } else if (isa<IntToPtrInst>(Base) &&
             Base->getName().contains("fieldarmor")) {
    LLVM_DEBUG(dbgs() << " GEP SOURCE is an instrumented alloca: " << *Base
                      << "\n");
    return false; // it's an instrumented alloca

  } else if (isa<LoadInst>(Base)) {
    LLVM_DEBUG(dbgs() << " GEP SOURCE is LOAD: " << *Base << "\n");
    // LLVM_DEBUG(
    //     dbgs()
    //     << " TODO: HANDLE ME AT LTO -> THIS MIGHT BE DEFINED IN ANOTHER "
    //        "FUNCTION of the same module, or in another module?\n");
    Value *loadOperand = cast<LoadInst>(Base)->getPointerOperand();
    // TODO: might be that some values come from intToPtr, dont know why
    // NOTE : if there are multiple stores, what do you do? Conservatively say
    // it;s dyn alloc.

    for (auto &U : loadOperand->uses()) {
      if (auto *storeInst = dyn_cast<StoreInst>(U.getUser())) {
        LLVM_DEBUG(dbgs() << " Found store op: " << *storeInst << "\n");
        Value *whatIsStored = storeInst->getValueOperand();
        if (isa<CallInst>(whatIsStored)) {

          CallInst *CI = cast<CallInst>(whatIsStored);
          Function *CalledFunc = CI->getCalledFunction();

          if (CalledFunc) {
            StringRef FuncName = CalledFunc->getName();
            if (FuncName.contains("malloc") || FuncName.contains("calloc") ||
                FuncName.contains("realloc") ||
                FuncName.contains("alligned_alloc") ||
                FuncName.contains("memalign") || FuncName.contains("valloc") ||
                FuncName.contains("posix_memalign")) {
              LLVM_DEBUG(dbgs() << " GEP source comes from malloc-like "
                                   "function via load/store: "
                                << FuncName << "\n");
              *endOfTheChain = CI;
              return true; // Found a malloc-like function
            }
          }
        } else if (isa<LoadInst>(whatIsStored)) {
          LLVM_DEBUG(dbgs() << " Things are pretty fucked up here: "
                            << *whatIsStored << "\n");
          return true;
        }

        return true; // TODO: review this
      }
    } // for uses

    LLVM_DEBUG(dbgs() << " GEP SOURCE is UNKNOWN: " << *Base << "\n");
    LLVM_DEBUG(dbgs() << " GEP TYPE is: ");
    Base->getType()->print(dbgs());
    LLVM_DEBUG(dbgs() << "\n");
    return true;
  } // if load

  return true; // DEFAULT
}

void HWAddressSanitizer::InstrumentGEP(GetElementPtrInst *GEPI) {
  dumpGEPDebug(GEPI);
  auto nOperands = GEPI->getNumOperands();
  assert(nOperands <= 3); // I expect 3 at most TODO: CHECK ON THIS

  /**
   * NOTE: this does not work, assuming a dbg instruction with the type is
   * there is not reliable.
   */

  Instruction *endOfTheChain = nullptr;
  // NOTE: this must be an instruction!!!!!
  auto dynamicallyAllocated = isDynamicallyAllocated(GEPI, &endOfTheChain);
  auto fatherType = GEPI->getSourceElementType();

  if (dynamicallyAllocated) {
    LLVM_DEBUG(dbgs() << "[FieldArmor] GEP on dynamically allocated memory ->"
                      << *GEPI << "\n");
    if (endOfTheChain) {
      LLVM_DEBUG(dbgs() << "[FieldArmor] GEP CHAIN END: " << *endOfTheChain
                        << "\n");
      Value *size = nullptr;

      if (isa<CallInst>(endOfTheChain)) {
        CallInst *CI = cast<CallInst>(endOfTheChain);
        Function *CalledFunc = CI->getCalledFunction();
        if (CalledFunc) {
          StringRef FuncName = CalledFunc->getName();
          if (FuncName.contains("malloc")) {
            size = CI->getArgOperand(0);
          } else if (FuncName.contains("calloc")) {
            // TODO: debug case of calloc
            Value *num = CI->getArgOperand(0);
            Value *sizePerElem = CI->getArgOperand(1);
            IRBuilder<> IRBForSize(CI->getNextNonDebugInstruction());
            size = IRBForSize.CreateMul(
                num, sizePerElem); // INSERT THE REST AFTER THIS
          } else if (FuncName.contains("realloc")) {
            size = CI->getArgOperand(1);
          } else if (FuncName.contains("aligned_alloc")) {
            size = CI->getArgOperand(1);
          } else if (FuncName.contains("posix_memalign")) {
            size = CI->getArgOperand(2);
          }
        }
        if (size == nullptr) {
          LLVM_DEBUG(dbgs() << " [FieldArmor] Could not determine size for GEP "
                            << *GEPI << "\n");
          return;
        }

        IRBuilder<> IRB(endOfTheChain->getNextNonDebugInstruction());

        Value *tagBuffer = M.getNamedGlobal(fatherType->getStructName().str() +
                                            ".fieldarmor.tagvec");

        if (!tagBuffer) {
          LLVM_DEBUG(dbgs() << " [FieldArmor] No tag buffer found for struct "
                            << fatherType->getStructName() << "\n");
          return;
        }

        Value *sizeCast = IRB.CreateZExtOrBitCast(size, Int64Ty);

        FunctionCallee fieldarmor_tag_memory = M.getOrInsertFunction(
            "fieldarmor_tag_memory", PtrTy, PtrTy, PtrTy, Int64Ty);
        Value *taggedPtr = IRB.CreateCall(fieldarmor_tag_memory,
                                          {endOfTheChain, tagBuffer, sizeCast});
        // do I have to CAST?
        // is ret assignable to taggedPtr like this?
        // taggedPtr->setName("fieldarmor.malloced.taggedptr");

        endOfTheChain->replaceUsesWithIf(
            taggedPtr, [endOfTheChain, taggedPtr](const Use &U) {
              auto *User = U.getUser();
              return User != endOfTheChain && User != taggedPtr &&
                     !isa<LifetimeIntrinsic>(User);
            });
      } // if isa<CallInst>
      else {
        LLVM_DEBUG(dbgs() << " [FieldArmor] No end of the chain found for GEP "
                          << *GEPI << "\n");
      }
    }
  } // if dynamically allocated

  if (!fatherType->isStructTy()) {
    LLVM_DEBUG(
        dbgs()
        << " [FieldArmor] Skipping GEP instrumentation: source type is not "
           "struct\n"); // TODO: handle this case properly, what
                        // happens with arrays?
    return;
  }

  IRBuilder<> IRB(GEPI->getNextNonDebugInstruction());

  auto sonType = GEPI->getResultElementType();
  // IRB.SetInsertPoint(GEPI->getNextNode()); // NOTE: this does not work
  // since after 1-2 instructions, it wont do anything, not even fail or
  // raise an error cases a) outer root pointer accesses non aggregate b)
  // outer root pointer accesses aggregate (struct/union) c) inner pointer
  // accesses non aggregate d) inner pointer accesses aggregate
  // (struct/union)

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
    Value *expectedSonT = IRB.CreateURem(IRB.CreateAdd(fatherT, sonIdx),
                                         ConstantInt::get(IntptrTy, 0x10Lu));

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

// Filter out non aggregate globals.
void HWAddressSanitizer::instrumentGlobal(GlobalVariable *GV) {

  Constant *Initializer = GV->getInitializer();
  Type *type = Initializer->getType();

  assert(type->isAggregateType() &&
         "[FieldArmor] Expected only aggregate types to be instrumented");
  if (type->isArrayTy()) {
    LLVM_DEBUG(
        dbgs() << "[FieldArmor] GLOBAL ARRAY OF STRUCTS INSTRUMENTATION: "
               << GV->getName() << ", come back later ... \n");
    return;
  } // if array -> this case should already be handled

  if (type->isStructTy()) {
    StructType *ST = dyn_cast<StructType>(type);
    // NOW CHECK IF LITERAL
    if (ST->isLiteral()) {
      // USE HASHING IN THIS CASE TODO TODO TODO

      LLVM_DEBUG(
          dbgs() << "[FieldArmor] Skipping instrumentation of literal struct "
                 << GV->getName() << "\n");
      return;
    }
    // TODO: handle unions!!!
  }

  uint8_t Tag = 0b10000000;
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

  auto *DescriptorTy =
      StructType::get(Int32Ty, Int32Ty, Int32Ty,
                      Int32Ty); // addr, info, tagvec ptr, padding ->
                                // preserve original alignment (8)
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

    // NOTE: if the struct is a literal struct, getStructName cannot be
    // called.
    auto *TagVector =
        M.getNamedGlobal(type->getStructName().str() + ".fieldarmor.tagvec");
    // else if (type->isArrayTy()) {

    // }
    assert(TagVector &&
           "Tag vector global must exist and be properly initialized.");
    auto *TVRelPtr = ConstantExpr::getTrunc(
        ConstantExpr::getSub(ConstantExpr::getPtrToInt(TagVector, Int64Ty),
                             ConstantExpr::getPtrToInt(Descriptor, Int64Ty)),
        Int32Ty);

    uint32_t Size = std::min(SizeInBytes - DescriptorPos, MaxDescriptorSize);
    auto *SizeAndTag = ConstantInt::get(Int32Ty, Size);
    Descriptor->setComdat(NewGV->getComdat());
    Descriptor->setInitializer(
        ConstantStruct::getAnon({GVRelPtr, SizeAndTag, TVRelPtr,
                                 TVRelPtr})); // PADDING -> not sure about this
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
  NumInstrumentedGlobals++;
}

void HWAddressSanitizer::instrumentGlobals() {
  std::vector<GlobalVariable *> Globals;
  LLVM_DEBUG(dbgs() << "[FieldArmor] ---- GLOBAL INSTRUMENTATION ---- \n");
  // TODO: add statistic to check on how many globals are not protected
  // TODO unions
  for (GlobalVariable &GV :
       M.globals()) { // NOTE: I think this does not take internal vars.

    if (GV.hasSanitizerMetadata() && GV.getSanitizerMetadata().NoHWAddress)
      continue;

    if (GV.isDeclarationForLinker() || GV.getName().starts_with("llvm.") ||
        GV.isThreadLocal())
      continue;

    // Common symbols can't have aliases point to them, so they can't be
    // tagged.
    if (GV.hasCommonLinkage())
      continue;
    if (GV.getName().contains("tagvec"))
      continue;
    // Globals with custom sections may be used in __start_/__stop_
    // enumeration, which would be broken both by adding tags and
    // potentially by the extra padding/alignment that we insert.
    if (GV.hasSection())
      continue;
    // WHAT HAPPEN IF A GLOBAL HAS NO INITIALIZER?

    if (GV.getValueType()->isArrayTy()) {
      // TODO handle matrix of structs
      LLVM_DEBUG(dbgs() << "[FieldArmor] Global array found.");
      LLVM_DEBUG(dbgs() << "\t Name: " << GV.getName() << "\n");
      LLVM_DEBUG(dbgs() << "\t Element type: ");
      LLVM_DEBUG(GV.getValueType()->getArrayElementType()->print(dbgs()));
      LLVM_DEBUG(dbgs() << "\n");

      if (!GV.getValueType()->getArrayElementType()->isStructTy()) {
        LLVM_DEBUG(dbgs() << "[FieldArmor]\tSkipping global array: "
                          << GV.getName() << "\n");
        LLVM_DEBUG(dbgs() << "\t\tELEM TYPE ");
        LLVM_DEBUG(GV.getValueType()->getArrayElementType()->print(dbgs()));
        LLVM_DEBUG(dbgs() << "\n");
        continue;
      }
    } // if it's an array

    else if (!GV.getValueType()->isStructTy()) {
      LLVM_DEBUG(dbgs() << "[FieldArmor] NOT A STRUCT: " << GV.getName()
                        << "\n");
      LLVM_DEBUG(dbgs() << "\t");
      LLVM_DEBUG(GV.getValueType()->print(dbgs()));
      LLVM_DEBUG(dbgs() << "\n");
      continue;
    } // Q: can I do the check on the initializer? Or it breaks?

    Globals.push_back(&GV);
  }
  // NOTE: I am assuming all the above checks are necessary.
  for (GlobalVariable *GV : Globals) {
    LLVM_DEBUG(dbgs() << "[FieldArmor] Global struct to instrument: "
                      << GV->getName() << "\n");
    // TODO: REENABLE
    // for (auto *U : GV->users()) {
    //   if (dyn_cast<ConstantExpr>(U) &&
    //       cast<ConstantExpr>(U)->getOpcode() == Instruction::GetElementPtr)
    //       {
    //     LLVM_DEBUG(dbgs() << "  CONST GEP (const expr): ");
    //     LLVM_DEBUG(U->print(dbgs()));
    //     LLVM_DEBUG(dbgs() << "\n");
    //     // InstrumentGEP(cast<GetElementPtrInst>(U)); // NOOOO
    //     InstrumentConstGEP(cast<ConstantExpr>(U),
    //                        GV->getInitializer()->getType());
    //   }
    // }
    instrumentGlobal(GV);
    // NOTE: replace uses first and then apply instrumentation
  } // for global var
}

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
  return ConstantInt::get(Int64Ty, 0b10000000);
}

// TODO: remove

void HWAddressSanitizer::createTagVector(StructType *t) {
  if (t->isLiteral()) { // TODO: handle literal structs.
    // THIS SEEMS TO BE A PROBLEM ONLY IN GLOBALS...
    ++NumLiteralStructs;
    LLVM_DEBUG(
        dbgs()
        << "[FieldArmor - createTagVector] NO PRECOMP FOR LITERAL STRUCT: "
        << t->getName() << "\n");
    return;
  }

  std::string TagVecName = t->getStructName().str() + ".fieldarmor.tagvec";
  auto *TagVec = M.getGlobalVariable(TagVecName, true);
  if (TagVec) {
    LLVM_DEBUG(dbgs() << "[FieldArmor - createTagVector] Tag vector already "
                         "exists for struct: "
                      << t->getName() << "\n");
    return;
  }
  auto size = M.getDataLayout().getTypeAllocSize(t);

  bool isUnion = t->getName().str().find("union.") != std::string::npos;
  u_int8_t *tags = nullptr;
  if (isUnion) {
    // create constant tag vector with all 1s
    LLVM_DEBUG(dbgs() << " [FieldArmor - createTagVector] Tagging union with "
                         "constant tag. Type ");
    LLVM_DEBUG(t->print(dbgs()));
    LLVM_DEBUG(dbgs() << "\n");
    tags = new uint8_t[size]; // TODO: get rid of this, maybe causing OOM
    memset(tags, 0x1, size);
    NumProtectedUnions++;
  } // if isUnion
  else {
    LLVM_DEBUG(dbgs() << " [FieldArmor - createTagVector] Its not a union: "
                      << t->getName() << "\n");
    tags = computeTags(t);
  }

  ArrayType *TagArrayType = ArrayType::get(Int8Ty, size);
  std::vector<llvm::Constant *> Elements(size,
                                         llvm::ConstantInt::get(Int8Ty, 0));
  for (int i = 0; i < size; i++) {
    Elements[i] = llvm::ConstantInt::get(Int8Ty, tags[i]);
  }
  delete[] tags; // NOTE: is it responsibility of the caller to delete

  llvm::Constant *Init = llvm::ConstantArray::get(TagArrayType, Elements);
  auto *NewTagVector_global = new GlobalVariable(
      M, TagArrayType, true, GlobalVariable::PrivateLinkage, Init, TagVecName);
  NewTagVector_global->setSection("hwanal_global"); // is this better?
  appendToCompilerUsed(M, NewTagVector_global); // does this break something?
  LLVM_DEBUG(dbgs() << " [FieldArmor - createTagVector] Created global "
                       "variable for type tag vector: "
                    << NewTagVector_global->getName() << "\n");
  NumDefinedTagVectors++;
}

void dbgPrintStructType(StructType *t) {
  bool isUnion = false;
  isUnion = t->getName().str().find("union.") != std::string::npos;
  LLVM_DEBUG(dbgs() << "[FieldArmor - createTagVectors] Identified struct: "
                    << t->getName() << "\n");
  LLVM_DEBUG(dbgs() << "\t\ttype: ");
  LLVM_DEBUG(t->print(dbgs()));
  LLVM_DEBUG(dbgs() << "\n");
  LLVM_DEBUG(dbgs() << "\t\tisLiteral: " << t->isLiteral() << "\n");
  LLVM_DEBUG(dbgs() << "\t\tisOpaque: " << t->isOpaque() << "\n");
  LLVM_DEBUG(dbgs() << "\t\tisSized: " << t->isSized() << "\n");
  LLVM_DEBUG(dbgs() << "\t\tisUnion: " << isUnion << "\n");
}

void HWAddressSanitizer::createTagVectors() {
  /** you only do this for each struct... */
  auto identifiedStructTypes = M.getIdentifiedStructTypes();

  for (auto t : identifiedStructTypes) {
    dbgPrintStructType(t);
    createTagVector(t);
  }
}

u_int8_t *HWAddressSanitizer::computeTags(StructType *Ty) {

  Value *PaddingTag = ConstantInt::get(Int8Ty, 0); // TODO
  // can we tell padding apart from real members? Dont know but Memsetting
  // tags vector to 0 tags padding with 0.

  DataLayout DL = M.getDataLayout(); // What if the type is defined elsewhere?
                                     // TODO: check on this
  u_int8_t *tags = new u_int8_t[DL.getTypeAllocSize(Ty)];
  memset(tags, 0, DL.getTypeAllocSize(Ty));

  assert(tags && "Could not allocate tags array");
  std::deque<std::tuple<Type *, uint8_t, uint8_t, uint8_t, size_t>> AggQueue;

  auto levelZeroFieldsOffsets = DL.getStructLayout(Ty)->getMemberOffsets();

  uint8_t fatherT = 0;
  uint8_t fatherL = 0;
  uint16_t sonIdx = 1; // NOTE: 2^^16 max number of fields
  if (levelZeroFieldsOffsets.size() >= (1 << 16) - 1) {

    LLVM_DEBUG(dbgs() << " [FieldArmor] Struct has TOO MANY FIELDS (> 65536), "
                         "skipping tag vector computation\n");
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

    if (sonType->isStructTy()) {
      auto structTy = cast<StructType>(sonType);
      if (structTy->isLiteral()) {
        // NOTE: getName fires an assertion on literal structs
        // NOTE: many std c++ types are implemented as literal structs
        LLVM_DEBUG(
            dbgs()
            << " [FieldArmor - ComputeTags] NO PRECOMP FOR LITERAL STRUCT: ");
        LLVM_DEBUG(sonType->print(dbgs()));
        LLVM_DEBUG(dbgs() << "\n");
        ++NumLiteralStructs;
        // continue;
      } else {
        bool nestedUnion =
            structTy->getStructName().str().find("union.") != std::string::npos;
        if (nestedUnion) {
          LLVM_DEBUG(dbgs()
                     << " [FieldArmor - ComputeTags] Identified nested union "
                        "struct tagging. Type ");
          LLVM_DEBUG(sonType->print(dbgs()));
          LLVM_DEBUG(dbgs() << "\n");
        }
      }

      // uint8_t sonT =
      //     (fatherT + sonIdx) % 16; // tag of ptr to this field, expected tag
      // uint8_t sonMask = sonType->getNumContainedTypes() % 16u;
      // auto rotatedMask = rotateOn4bits(sonMask, sonIdx);
      // auto newBaseTag = (rotatedMask ^ sonT);

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
            std::make_tuple(subtype, newBaseTag, (fatherL + 1) % 8,
                            sonSubfieldsCount - count, currSonSubfieldOffset));
        count++;
      } // for subtype

    } else if (sonType->isArrayTy()) { // TODO: handle multidimensional arrays
                                       // of structs

      Type *elementType = sonType->getArrayElementType();

      if (elementType->isStructTy()) {
        LLVM_DEBUG(
            dbgs()
            << " [FieldArmor - ComputeTags] Tagging array of structs. Type ");
        LLVM_DEBUG(sonType->print(dbgs()));
        LLVM_DEBUG(dbgs() << "\n");

        auto structType = cast<StructType>(elementType);
        auto structName = structType->getStructName().str();

        auto tagVectorGlobal = M.getGlobalVariable(
            structName + ".fieldarmor.tagvec",
            true); // CAVEAT -> these are for internal use...

        if (!tagVectorGlobal) {
          LLVM_DEBUG(dbgs() << " [FieldArmor - ComputeTags] No precomputed tag "
                               "vector for struct "
                            << structName << " found. Creating it.\n");

          createTagVector(structType);
        }
        tagVectorGlobal =
            M.getGlobalVariable(structName + ".fieldarmor.tagvec", true);
        if (!tagVectorGlobal) {
          LLVM_DEBUG(dbgs() << " [FieldArmor - ComputeTags] STILL No "
                               "precomputed tag vector for struct "
                            << structName
                            << " found. Skipping array of structs tagging.\n");
          continue;
        }
        // APPLY THIS FUCKING VECTOR
        Constant *tagVectorInit =
            cast<Constant>(tagVectorGlobal->getInitializer());

        uint64_t elementSize = DL.getTypeAllocSize(elementType);
        uint64_t arraySize = DL.getTypeAllocSize(sonType);
        uint64_t numElements = arraySize / elementSize;

        for (int k = 0; k < numElements; k++) {
          uint64_t elemOffset = sonOffset + k * elementSize;

          for (int i = 0; i < elementSize; i++) {
            tags[elemOffset + i] = static_cast<uint8_t>(
                cast<ConstantInt>(tagVectorInit->getAggregateElement(i))
                    ->getZExtValue());
          }
        } // for each struct, copy its tag vector at the right position
      } // if array of structs

      else {
        LLVM_DEBUG(
            dbgs()
            << " [FieldArmor - computeTags] Tagging array of scalars. Type ");
        LLVM_DEBUG(sonType->print(dbgs()));
        LLVM_DEBUG(dbgs() << "\n");

        // tag the array as a memory location
        uint8_t sonT = (fatherT + sonIdx) % 16;
        uint8_t sonTag = sonT | (fatherL << 4);

        assert((sonT & 0x80) == 0 &&
               "ROOT POINTER BIT must be set to 0 in memory tags");

        uint64_t sonSize = DL.getTypeAllocSize(sonType);
        for (uint64_t i = 0; i < sonSize; i++) {
          tags[sonOffset + i] = sonTag;
        }
      }

    } // if array

    else {
      // scalar fields
      LLVM_DEBUG(
          dbgs() << " [FieldArmor - computeTags] Tagging scalar field. Type ");
      LLVM_DEBUG(sonType->print(dbgs()));
      LLVM_DEBUG(dbgs() << "\n");
      uint8_t sonT = (fatherT + sonIdx) % 16;
      uint8_t sonTag = sonT | (fatherL << 4);

      assert((sonT & 0x80) == 0 &&
             "ROOT POINTER BIT must be set to 0 in memory tags");

      int sonSize = DL.getTypeAllocSize(sonType);
      for (int i = 0; i < sonSize; i++) {
        tags[sonOffset + i] = sonTag;
      }

    } // else scalar fields
  } // while agg queue not empty
  return tags;
} // computeTags

void HWAddressSanitizer::InstrumentConstGEP(ConstantExpr *GEPI,
                                            Type *fatherType) {
  /** DEBUG */
  FunctionCallee PrintfFunc = M.getOrInsertFunction(
      "printf", FunctionType::get(Int32Ty, {PtrTy}, true));
  /** DEBUG */

  auto nOperands = GEPI->getNumOperands();
  assert(nOperands <= 3); // I expect 3 at most TODO: CHECK ON THIS
  Instruction *insertBefore = nullptr;
  // IDEA: insert instrumentation before every user of the const GEP.
  auto users = GEPI->users();
  LLVM_DEBUG(dbgs() << " [FieldArmor] CONST GEP has " << GEPI->getNumUses()
                    << " users\n");
  if (!users.empty()) {

    auto *one_user = *users.begin();
    if (Instruction *one_user_inst = dyn_cast<Instruction>(one_user)) {
      LLVM_DEBUG(dbgs() << "\tuser for CONST GEP: ");
      LLVM_DEBUG(one_user_inst->print(dbgs()));
      LLVM_DEBUG(dbgs() << "\n");

      insertBefore = one_user_inst->getPrevNode();
    }
    if (!insertBefore) {
      LLVM_DEBUG(dbgs() << "\t[FieldArmor] Skipping CONST GEP "
                           "instrumentation: no valid user "
                           "instruction found\n");
      return;
    }
  }
  auto *constIdx = dyn_cast<ConstantInt>(GEPI->getOperand(2));
  if (!constIdx) {
    LLVM_DEBUG(dbgs() << " [FieldArmor] CONST GEP index is not constant\n");
    return;
  }
  uint64_t gepIdx = constIdx->getZExtValue();
  auto sonType = fatherType->getContainedType(gepIdx);

  LLVM_DEBUG(dbgs() << "[FieldArmor] CONST GEP TYPES: src: ");
  LLVM_DEBUG(fatherType->print(dbgs()));
  LLVM_DEBUG(dbgs() << "\n");
  LLVM_DEBUG(dbgs() << " \t[FieldArmor] dst: ");
  LLVM_DEBUG(sonType->print(dbgs()));
  LLVM_DEBUG(dbgs() << "\n");

  IRBuilder<> IRB(M.getContext());
  IRB.SetInsertPoint(insertBefore);
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
  // DEBUG
  // Value *FormatStr =
  //     IRB.CreateGlobalString("[ConstGEPINST] FT: %08x FL: %08x\n");
  // IRB.CreateCall(PrintfFunc,
  //                {FormatStr, fatherT, fatherL});
  // END DEBUG
  Value *sonTag = nullptr;

  if (!sonType->isStructTy()) {
    Value *sonT = IRB.CreateURem(IRB.CreateAdd(fatherT, sonIdx),
                                 ConstantInt::get(IntptrTy, 0x10Lu));
    sonTag = IRB.CreateOr(sonT, fatherL);
    // DEBUG
    // Value *FormatStr2 =
    //     IRB.CreateGlobalString("[ConstGEPINST] SON STRUCT TYPE, SON T:
    //     %08x\n");
    // IRB.CreateCall(PrintfFunc,
    //                {FormatStr2, sonT});
    // END DEBUG
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
    Value *expectedSonT = IRB.CreateURem(IRB.CreateAdd(fatherT, sonIdx),
                                         ConstantInt::get(IntptrTy, 0x10Lu));

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
} // instrumentConstGEP