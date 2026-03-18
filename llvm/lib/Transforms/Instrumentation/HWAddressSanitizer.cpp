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
#define TRANS_CONSTANT 0x400000000000ULL // 1<<46, 0x400000000000
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

// FSAN KNOBS
bool ptrTagging = true;
static cl::opt<bool>
    ClFSAN_GEP("fsan-instrument-geps",
               cl::desc("instrument getelementptr instructions"), cl::Hidden,
               cl::init(ptrTagging));

static cl::opt<bool> ClFSAN_BOP("fsan-instrument-bops",
                                cl::desc("instrument binary op instructions"),
                                cl::Hidden, cl::init(false));

static cl::opt<bool> ClFSAN_CMP("fsan-instrument-cmp",
                                cl::desc("instrument compare instructions"),
                                cl::Hidden, cl::init(ptrTagging));

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
    ClInstrumentLandingPads("hwasan-instrument-landing-pads",
                            cl::desc("instrument landing pads"), cl::Hidden,
                            cl::init(false));

static cl::opt<bool> ClInstrumentPersonalityFunctions(
    "hwasan-instrument-personality-functions",
    cl::desc("instrument personality functions"), cl::Hidden, cl::init(false));

namespace {

template <typename T> T optOr(cl::opt<T> &Opt, T Other) {
  return Opt.getNumOccurrences() ? Opt : Other;
}

bool shouldInstrumentStack(const Triple &TargetTriple) { return ClFSAN_stack; }

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
  u_int64_t RPTag = 0x0LU;
  void InstrumentGEP(GetElementPtrInst *GEPI);
  void InstrumentBOP(BinaryOperator *BOP);
  StructType *getStructTypeFromDbgInfo(GlobalVariable *GV, int *numElements,
                                       bool *isUnion);
  void InstrumentStoreOfFunctionArg(StoreInst *SI);
  Type *figureOutInheritance(const std::set<Type *> &structTypes);
  Value *GetArraySize(CallBase *CI, StructType *t,
                      IRBuilder<> &IRB); // FieldArmor
  void handleGEP2operands(GetElementPtrInst *GEPI);
  void InstrumentCMP(CmpInst *CI);
  void InstrumentConstGEP(ConstantExpr *GEPI); // TODO
  Value *getRPTag(IRBuilder<> &IRB);           // FieldArmor
  Value *ApplyRLT(IRBuilder<> &IRB, Instruction *AI, Type *rootType,
                  const DataLayout &DL); // TODO: refactor remove DL

  u_int8_t *computeTags(StructType *t);             // FieldArmor
  void createTagVectors();                          // FieldArmor
  void createTagVector(StructType *t);              // FieldArmor
  Value *RetrieveOrCreateTagVector(StructType *Ty); // FieldArmor
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

  void tagAlloca(IRBuilder<> &IRB, AllocaInst *AI, const DataLayout &DL);
  void untagAlloca(IRBuilder<> &IRB, AllocaInst *AI, const DataLayout &DL);
  Value *tagPointer(IRBuilder<> &IRB, Type *Ty, Value *PtrLong, Value *Tag);
  Value *untagPointer(IRBuilder<> &IRB, Value *PtrLong);
  Value *untagPointerIntrinsic(IRBuilder<> &IRB, Value *Ptr);
  bool instrumentStack(memtag::StackInfo &Info, const DominatorTree &DT,
                       const PostDominatorTree &PDT, const LoopInfo &LI,
                       const DataLayout &DL);
  bool instrumentLandingPads(SmallVectorImpl<Instruction *> &RetVec);
  Value *getNextTagWithCall(IRBuilder<> &IRB); // not sure I still need this

  Value *getHwasanThreadSlotPtr(IRBuilder<> &IRB);
  Value *applyTagMask(IRBuilder<> &IRB, Value *OldTag);
  unsigned retagMask(unsigned AllocaNo);
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
  ///   shadow = (mem>>Scale) + align_up(__hwasan_shadow,
  ///   kShadowBaseAlignment)
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
  RetrievedTypes =
      &MAM.getResult<TypeReconstructionAnalysis>(M); // TODO: remove
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
  errs() << "[FSAN] MEM ACCESS" << (ClFSAN_memAccesses ? " ON\n" : " OFF\n");
  errs() << "[FSAN] MEM INTRIN" << (ClFSAN_memIntr ? " ON\n" : " OFF\n");
  errs() << "[FSAN] STACK" << (ClFSAN_stack ? " ON\n" : " OFF\n");
  errs() << "[FSAN] GLOBALS " << (ClFSAN_globals ? " ON\n" : " OFF\n");
  errs() << "[FSAN] BOP " << (ClFSAN_BOP ? " ON\n" : " OFF\n");
  errs() << "[FSAN] CMP " << (ClFSAN_CMP ? " ON\n" : " OFF\n");
  errs() << "[FSAN] GEP " << (ClFSAN_GEP ? " ON\n" : " OFF\n");

  unsigned PtrBits = M.getDataLayout().getPointerTypeSizeInBits(PtrTy);
  Type *MaskTy = IntegerType::get(M.getContext(), PtrBits);
  Function *PtrMask =
      Intrinsic::getDeclaration(&M, Intrinsic::ptrmask, {PtrTy, MaskTy});
  errs() << "[FSAN] PointerMask intrinsic: "
         << (PtrMask ? "FOUND\n" : "NOT FOUND\n");
  PointerTagShift = IsX86_64 ? 57 : 56;
  TagMaskByte = IsX86_64 ? 0x3F : 0xFF;
  // errs() << "[DBGDBG] PointerTagShift: " << PointerTagShift
  //        << ", TagMaskByte: " << (unsigned)TagMaskByte << "\n";
  Mapping.init(TargetTriple, InstrumentWithCalls, CompileKernel);

  C = &(M.getContext());
  IRBuilder<> IRB(*C);

  HwasanCtorFunction = nullptr;

  // Older versions of Android do not have the required runtime support for
  // short granules, global or personality function instrumentation. On other
  // platforms we currently require using the latest version of the runtime.
  bool NewRuntime =
      !TargetTriple.isAndroid() || !TargetTriple.isAndroidVersionLT(30);

  // OutlinedChecks = (TargetTriple.isAArch64() || TargetTriple.isRISCV64()) &&
  //                  TargetTriple.isOSBinFormatELF() &&
  //                  !optOr(ClInlineAllChecks, Recover);

  // These platforms may prefer less inlining to reduce binary size.
  // InlineFastPath = optOr(ClInlineFastPathChecks, !(TargetTriple.isAndroid()
  // ||
  //                                                  TargetTriple.isOSFuchsia()));

  if (ClMatchAllTag.getNumOccurrences()) {
    if (ClMatchAllTag != -1) {
      MatchAllTag = ClMatchAllTag & 0xFF;
    }
  } else if (CompileKernel) {
    MatchAllTag = 0xFF;
  }
  UseMatchAllCallback = !CompileKernel && MatchAllTag.has_value();

  // If we don't have personality function support, fall back to landing pads.
  InstrumentLandingPads = optOr(ClInstrumentLandingPads, true); // DEBUG

  InstrumentGlobals = optOr(ClFSAN_globals, true);

  if (!CompileKernel) {
    createHwasanCtorComdat(); // creates the routine ctor with a call into the
                              // runtime function __hwasan_init

    createTagVectors();
    if (InstrumentGlobals) {
      errs() << "[FSAN] GLOBAL ON\n";
      instrumentGlobals();
    } else
      errs() << "[FSAN] GLOBAL OFF\n";

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
                                         DomTreeUpdater &DTU, LoopInfo *LI) {}

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

  // extend ptr tag
  switch (AccessSizeIndex) {
  case 0:
    // errs() << "[FSAN] 1B access \n";
    // InsertBefore->dump();
    // errs() << "\n";
    R.MemTag = IRB.CreateLoad(R.PtrTag->getType(), Shadow);

    TagMismatch = IRB.CreateICmpNE(
        R.PtrTag,
        IRB.CreateAnd(R.MemTag, ConstantInt::get(R.PtrTag->getType(), 0x0FUL)));
    break;
  case 1:
    // errs() << "[FSAN] 2B access \n";
    // InsertBefore->dump();
    // errs() << "\n";
    R.PtrTag = IRB.CreateZExt(R.PtrTag, Int16Ty);
    R.PtrTag = IRB.CreateMul(R.PtrTag, ConstantInt::get(Int16Ty, 0x0101UL));
    R.MemTag = IRB.CreateLoad(R.PtrTag->getType(), Shadow); // always fetch 64B
    TagMismatch = IRB.CreateICmpNE(
        R.PtrTag, IRB.CreateAnd(R.MemTag, ConstantInt::get(R.PtrTag->getType(),
                                                           0x0F0FUL)));
    break;
  case 2:
    // errs() << "[FSAN] 4B access \n";
    // InsertBefore->dump();
    // errs() << "\n";
    R.PtrTag = IRB.CreateZExt(R.PtrTag, Int32Ty);
    R.PtrTag = IRB.CreateMul(R.PtrTag, ConstantInt::get(Int32Ty, 0x01010101UL));
    R.MemTag = IRB.CreateLoad(R.PtrTag->getType(), Shadow); // always fetch 64B
    TagMismatch = IRB.CreateICmpNE(
        R.PtrTag, IRB.CreateAnd(R.MemTag, ConstantInt::get(R.PtrTag->getType(),
                                                           0x0F0F0F0FUL)));
    break;
  case 3:
    // errs() << "[FSAN] 8B access \n";
    // InsertBefore->dump();
    // errs() << "\n";
    R.PtrTag = IRB.CreateZExt(R.PtrTag, Int64Ty);
    R.PtrTag = IRB.CreateMul(R.PtrTag,
                             ConstantInt::get(Int64Ty, 0x0101010101010101ULL));
    R.MemTag = IRB.CreateLoad(R.PtrTag->getType(), Shadow); // always fetch 64B
    TagMismatch = IRB.CreateICmpNE(
        R.PtrTag,
        IRB.CreateAnd(R.MemTag, ConstantInt::get(R.PtrTag->getType(),
                                                 0x0F0F0F0F0F0F0F0FULL)));
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
    R.MemTag = IRB.CreateLoad(R.PtrTag->getType(), Shadow);
    APInt MaskPattern(128, "0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F", 16);
    R.MemTag = IRB.CreateAnd(R.MemTag, ConstantInt::get(Int128Ty, MaskPattern));
    TagMismatch = IRB.CreateICmpNE(R.PtrTag, R.MemTag);
    break;
  }
  assert(R.MemTag && "MemTag should have been set in the switch statement");
  // R.MemTag->setName("fsan.memtag");

  Value *MemoryIsTagged =
      IRB.CreateICmpNE(R.MemTag, ConstantInt::get(R.MemTag->getType(), 0x0UL));
  // MemoryIsTagged->setName("fsan.memory_is_tagged");
  Value *PtrIsTagged =
      IRB.CreateICmpNE(R.PtrTag, ConstantInt::get(R.PtrTag->getType(), 0x0UL));
  // PtrIsTagged->setName("fsan.ptr_is_tagged");
  // set mem op as volatile

  Value *AllConditions = IRB.CreateAnd(PtrIsTagged, MemoryIsTagged);
  AllConditions = IRB.CreateAnd(AllConditions, TagMismatch);
  // AND: if (tag mismatch && memory is tagged && pointer is tagged)
  // Q: does
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

bool memcpyIsOOB(MemTransferInst *MTI, const DataLayout &DL) {
  // return true if statically sized memcpy calls write past the bounds of a
  // field
  // TODO
  return false;
}

void HWAddressSanitizer::instrumentMemIntrinsic(MemIntrinsic *MI) {
  bool untag_first = false;
  auto arg0 = MI->getOperand(0);
  auto arg1 = MI->getOperand(1);
  if (!MI->getMetadata("fsan.instrument"))
    return;
  // NOTE: the above may introduce FNs
  // NO FPs observed on SPEC though

  IRBuilder<> IRB(MI);

  // TODO: memmove
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

    SmallVector<Value *, 2> Args{IRB.CreatePointerCast(Addr, IntptrTy)};
    IRB.CreateCall(HwasanMemoryAccessCallback[O.IsWrite][AccessSizeIndex],
                   Args);
    // instrumentMemAccessInline(Addr, O.IsWrite, AccessSizeIndex, I, DTU, LI);
    // NumMemAccessesInlined++;

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
  /** Apply tag 0 to the previously tagged memory, immaterially of the type.
   */
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
    errs() << "[FSAN] WARNING: Alloca of VectorType for RLT not yet "
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
      // errs() << "[FSAN] Alloca of array of arrays "
      //  << *(AI->getAllocatedType()) << "\n";
      for (u_int64_t el = 0; el < AT->getNumElements(); el++) {
        auto *ElementPtr =
            IRB.CreateGEP(elementType, AI, {ConstantInt::get(Int64Ty, el)});
        // this points to an array
        GetElementPtrInst *i_th_array = cast<GetElementPtrInst>(ElementPtr);
        ArrayType *innerArrayType = cast<ArrayType>(elementType);
        uint64_t int_n = innerArrayType->getNumElements();
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
  return IRB.CreateCall(PtrMask, {Ptr, MaskVal});
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
    // errs() << "[FSAN] Instrumenting landing pad: " << *LP << "\n";
    // if (LandingPadInst *LPI = dyn_cast<LandingPadInst>(LP)) {
    //   // dump ptr and int
    //   LPI->dump();
    // }
    // IRBuilder<> IRB(LP->getNextNonDebugInstruction());
    // IRB.CreateCall(
    //     HwasanHandleVfork,
    //     {memtag::readRegister(
    //         IRB, (TargetTriple.getArch() == Triple::x86_64) ? "rsp" :
    //         "sp")});
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
    Value *Tag = nullptr;

    if (AllocaInst *AIcast = dyn_cast<AllocaInst>(AI)) {
      Type *allocatedType = AIcast->getAllocatedType();
      // NOTE: SPEC 2017 does not have literals on stack.
      if (allocatedType->isArrayTy()) {
        auto elementType = allocatedType->getArrayElementType();
        if (elementType->isStructTy()) {
          // 1D array
          StructType *ST_internal = dyn_cast<StructType>(elementType);
          if (ST_internal->isLiteral()) {
            continue;
          }

          else if (ST_internal->getName().str().find("union.") == 0) {
            continue;
          }
        } // case: 1d array of structs

        else if (elementType->isArrayTy()) {
          // multi-dimensional array
          auto innerElementType = elementType->getArrayElementType();
          if (innerElementType->isStructTy()) {
            StructType *ST_internal_l2 = dyn_cast<StructType>(innerElementType);
            if (ST_internal_l2->isLiteral()) {
              LiteralStructs++;
              continue;
            }

            else if (ST_internal_l2->getName().str().find("union.") == 0) {
              continue;
            }
          } // case: 2d array of structs
          else if (innerElementType->isArrayTy()) {
            continue; // TODO
          } else {
            continue;
          } // case: 2d array of scalars or other types I don't care about atm

        } // case 2d array

        else {
          continue;
        } // case : array of scalars/NA
      } // case : alloca of ARRAY

      if (!allocatedType->isStructTy()) {
        // not an array, not a struct
        continue;
      } else {
        // it's a struct
        StructType *ST = dyn_cast<StructType>(allocatedType);
        if (ST->isLiteral()) {
          continue;
        } else if (ST->getName().str().find("union.") == 0) {
          continue;
        }
      } // rules out allocas of not safe structs
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

    tagAlloca(IRB, AI, DL); // insert a call to fieldarmor_tag_memory
    // function

    // AI->replaceUsesWithIf(Replacement, [AICast, AILong](const Use &U) {
    //   auto *User = U.getUser();
    //   return User != AILong && User != AICast &&
    //   !isa<LifetimeIntrinsic>(User);
    // });

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
  NumTotalFuncs++;
  OptimizationRemarkEmitter &ORE =
      FAM.getResult<OptimizationRemarkEmitterAnalysis>(F);

  NumInstrumentedFuncs++;

  SmallVector<InterestingMemoryOperand, 16> OperandsToInstrument;
  SmallVector<MemIntrinsic *, 16> IntrinToInstrument;
  SmallVector<Instruction *, 8> LandingPadVec;

  // FieldArmor
  SmallVector<GetElementPtrInst *, 40> GEPsToInstrument;
  SmallVector<CmpInst *, 40> CMPsToInstrument;
  SmallVector<ConstantExpr *, 40> ConstGEPsToInstrument;
  SmallVector<StoreInst *, 40> StoresToInstrument;
  SmallVector<BinaryOperator *, 40> BOPsToInstrument;
  // FieldArmor

  const TargetLibraryInfo &TLI = FAM.getResult<TargetLibraryAnalysis>(F);

  memtag::StackInfoBuilder SIB(SSI, DEBUG_TYPE);
  // TODO: SIB might be removing UB -> check if we want to use this!
  for (auto &Inst : instructions(F)) {

    if (InstrumentStack) {
      SIB.visit(ORE, Inst);
    }

    if (InstrumentLandingPads && isa<LandingPadInst>(Inst))
      LandingPadVec.push_back(&Inst);

    // TODO: filter out something
    // TODO: I am ignoring ORE at the moment, I think it's fine to have the
    // RemarkEmitter emit info in SIB, just double check that it does not
    // break stuff.
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
    if (auto *BO = dyn_cast<BinaryOperator>(&Inst)) {
      if (BO->getOpcode() == Instruction::Sub) {
        // NOTE: only subs, because adding ptrs should be against the standard
        // NOTE: ptr subtractions make sense only if the two pointers point to
        // (parts of) the same object. Ow they are just undefined behavior.
        BOPsToInstrument.push_back(BO);
      }
    }

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(&Inst)) {
      if (CE->getOpcode() == Instruction::GetElementPtr) {
        // TODO: get rid of this and check at the store/load operand level.
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
  /** NOTE: what is currently instrumented
   * 1) GLOBALS
   * 2) STACK
   * 3) GEPs
   * 4) HEAP
   * 5) CMP
   * 6) BOPs with PtrToInt operands
   * the type of the struct they point to)
   */

  if (!SInfo.AllocasToInstrument.empty()) {
    const DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);
    const PostDominatorTree &PDT = FAM.getResult<PostDominatorTreeAnalysis>(F);
    const LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
    instrumentStack(SInfo, DT, PDT, LI, F.getDataLayout()); // KNOB
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

  // TODO: filter out checks.

  if (ClFSAN_memIntr && !IntrinToInstrument.empty()) {
    for (auto *Inst : IntrinToInstrument)
      instrumentMemIntrinsic(Inst); // KNOB
  }

  if (ClFSAN_GEP) {
    for (auto &GEPI : GEPsToInstrument) {
      InstrumentGEP(GEPI); // KNOB
    }
  }

  if (ClFSAN_BOP) {
    for (auto &BOP : BOPsToInstrument) {
      InstrumentBOP(BOP); // KNOB
    }
  }

  if (ClFSAN_CMP) {
    for (auto &CMPI : CMPsToInstrument) {
      InstrumentCMP(CMPI); // KNOB
    }
  }

  DominatorTree *DT = FAM.getCachedResult<DominatorTreeAnalysis>(F);
  PostDominatorTree *PDT = FAM.getCachedResult<PostDominatorTreeAnalysis>(F);
  LoopInfo *LI = FAM.getCachedResult<LoopAnalysis>(F);
  DomTreeUpdater DTU(DT, PDT, DomTreeUpdater::UpdateStrategy::Lazy);
  const DataLayout &DL = F.getDataLayout();
  if (ClFSAN_memAccesses)
    for (auto &Operand : OperandsToInstrument)
      instrumentMemAccess(Operand, DTU, LI, DL); // KNOB
  DTU.flush(); // TODO: does this have an interplay with optimizations?
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

Value *HWAddressSanitizer::GetArraySize(CallBase *CI, StructType *t,
                                        IRBuilder<> &IRB) {
  std::string demangledName =
      CI->getCalledFunction()
          ? demangle(CI->getCalledFunction()->getName().str())
          : "";
  if (demangledName == "") {
    return 0;
  }

  uint64_t typeSize = M.getDataLayout().getTypeAllocSize(t);

  if (typeSize == 0) {
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

  errs() << "[FSAN] WARNING: allocator not handled for size "
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

Value *HWAddressSanitizer::RetrieveOrCreateTagVector(StructType *t) {

  auto TagVector = M.getGlobalVariable(
      t->getStructName().str() + ".fieldarmor.tagvec", true);
  if (!TagVector) {
    createTagVector(t);
    TagVector = M.getGlobalVariable(
        t->getStructName().str() + ".fieldarmor.tagvec", true);
    return TagVector;
  }
  return TagVector;
}

void HWAddressSanitizer::handleGEP2operands(GetElementPtrInst *GEPI) {
  // EXAMPLE: GEP on ptr array
  // TODO: if necessary, tag RPs. For now, it's not needed.
  // if (GEPI->getType()->isStructTy() && !GEPI->getType()->isVectorTy()) {
  //   IRBuilder<> IRB(GEPI->getNextNonDebugInstruction());
  //   Value *resultLong =
  //       IRB.CreatePointerCast(GEPI, IntptrTy); // this breaks for some GEPs

  //   Value *untaggedResLong = untagPointer(IRB, resultLong);
  //   Value *taggedPointer =
  //       tagPointer(IRB, GEPI->getType(), untaggedResLong,
  //                  ConstantInt::get(IntptrTy, RPTag)); // set RP bit
  //   std::string Name = GEPI->hasName() ? GEPI->getName().str()
  //                                      : "gep." +
  //                                      itostr(NumInstrumentedGEPs);
  //   taggedPointer->setName(Name + ".fieldarmor.struct");
  //   GEPI->replaceUsesWithIf(taggedPointer, [resultLong](const Use &U) {
  //     auto *User = U.getUser();
  //     return User != resultLong && !isa<LifetimeIntrinsic>(User);
  //   });
  //   NumInstrumentedGEPs++;
  //   return;
  // }
}

// instrument all ptr subs -> each and every BOP sub is passed to this, method.
// TODO: FILTER!
void HWAddressSanitizer::InstrumentBOP(BinaryOperator *BOP) {
  auto DL = M.getDataLayout();
  errs() << " INSTRUMENTING BOP: ";
  BOP->print(errs());
  errs() << "\n";
  auto *retType = BOP->getType();
  auto bopUsers = BOP->users();

  auto *OP1 = BOP->getOperand(0);
  Value *PtrOperand1 = nullptr, *PtrOperand2 = nullptr;
  if (PtrToIntInst *PTI = dyn_cast<PtrToIntInst>(OP1)) {
    PtrOperand1 = PTI->getOperand(0);
  }
  auto *OP2 = BOP->getOperand(1);
  if (PtrToIntInst *PTI = dyn_cast<PtrToIntInst>(OP2)) {
    PtrOperand2 = PTI->getOperand(0);
  }

  /** A BAD EXAMPLE OF UB:
 BOP:   %sub.ptr.sub.i29.i326 = sub i64 %sub.ptr.lhs.cast.i.i316,
                                        %sub.ptr.rhs.cast.i28.i325
        >> PtrToInt 1:   %90 = load ptr, ptr %_M_finish.i.i314.fsan.scalar,
 align 8
        >> PtrToInt 2:   %add.ptr.i324.fsan.struct = call ptr
 @llvm.ptrmask.p0.i64(ptr %add.ptr.i324, i64 -9079256848778919937), !dbg !5273
*/
  // FIRST CHECK: if FSAN-untagged for sure, skip
  bool skip1 = true, skip2 = true;
  skip1 &= (OP1->hasName() &&
            OP1->getName().str().find(".fsan.struct") != std::string::npos);
  skip2 &= (OP2->hasName() &&
            OP2->getName().str().find(".fsan.struct") != std::string::npos);
  // SECOND CHECK: if the hypothetic ptrtoint operand has "fsan.scalar" in the
  // name, untag!
  skip1 &=
      !(PtrOperand1 && PtrOperand1->hasName() &&
        PtrOperand1->getName().str().find(".fsan.scalar") != std::string::npos);
  skip2 &=
      !(PtrOperand2 && PtrOperand2->hasName() &&
        PtrOperand2->getName().str().find(".fsan.scalar") != std::string::npos);
  // THIRD CHECK: whatever comes from a load ptr must be untagged, cannot be
  // skipped
  skip1 &= !(PtrOperand1 && isa<LoadInst>(PtrOperand1));
  skip2 &= !(PtrOperand2 && isa<LoadInst>(PtrOperand2));

  // FOURTH CHECK: whatever comes from a ptrmask is already untagged
  if (PtrOperand1)
    if (CallInst *CI = dyn_cast<CallInst>(PtrOperand1)) {
      auto *callee = CI->getCalledFunction();
      auto demangledName =
          callee && callee->hasName() ? demangle(callee->getName().str()) : "";
      bool isPtrMask =
          (callee && callee->hasName() &&
           callee->getName().str().find("llvm.ptrmask") != std::string::npos);
      if (isPtrMask)
        skip1 = true;
      errs() << ">> PtrOperand1 is call: " << *PtrOperand1
             << ", isPtrMask: " << isPtrMask << "\n";
    }
  // FIFTH CHECK: if ptr is null, skip
  // skip1 &= !(PtrOperand1 && isa<ConstantPointerNull>(PtrOperand1));
  // skip2 &= !(PtrOperand2 && isa<ConstantPointerNull>(PtrOperand2));
  
  // NOTE: this is still unsafe when PHIs are there, just my hunch
  if (PtrOperand2)
    if (CallInst *CI = dyn_cast<CallInst>(PtrOperand2)) {
      auto *callee = CI->getCalledFunction();
      auto demangledName =
          callee && callee->hasName() ? demangle(callee->getName().str()) : "";
      bool isPtrMask =
          (callee && callee->hasName() &&
           callee->getName().str().find("llvm.ptrmask") != std::string::npos);
      if (isPtrMask)
        skip2 = true;

      errs() << ">> PtrOperand2 is call: " << *PtrOperand2
             << ", isPtrMask: " << isPtrMask << "\n";
    }

  if (skip1 && skip2) {
    // if either of the above is false, you must not untag
    return;
  }

  // NOTE: this could open up to some FNs if the PtrToInt is reused in an
  // IntToPtr. Alternatively, create a new PtrToInt and use that one as operand
  // in the BOP.
  // TODO: optimize even more.
  if (!skip1 && PtrOperand1) {
    PtrToIntInst *PTI1 = dyn_cast<PtrToIntInst>(OP1);
    errs() << ">> PtrOperand1 " << *PtrOperand1 << "\n";
    llvm::KnownBits Known(DL.getPointerTypeSizeInBits(PtrOperand1->getType()));
    llvm::computeKnownBits(PtrOperand1, Known, DL);
    if (Known.isConstant() || Known.isAllOnes() || Known.isZero()) {
      errs() << ">> PtrOperand1 is constant, skipping untagging\n";
      return;
    }
    IRBuilder<> IRB(PTI1);
    auto *untaggedOP1 = untagPointerIntrinsic(IRB, PtrOperand1);
    PTI1->setOperand(0, untaggedOP1);
  }

  if (!skip2 && PtrOperand2) {
    PtrToIntInst *PTI2 = dyn_cast<PtrToIntInst>(OP2);
    errs() << ">> PtrOperand2 " << *PtrOperand2 << "\n";
    llvm::KnownBits Known(DL.getPointerTypeSizeInBits(PtrOperand2->getType()));
    llvm::computeKnownBits(PtrOperand2, Known, DL);
    if (Known.isConstant() || Known.isAllOnes() || Known.isZero()) {
      errs() << ">> PtrOperand2 is constant, skipping untagging\n";
      return;
    }
    IRBuilder<> IRB(PTI2);
    auto *untaggedOP2 = untagPointerIntrinsic(IRB, PtrOperand2);
    PTI2->setOperand(0, untaggedOP2);
  }
}

void HWAddressSanitizer::InstrumentGEP(GetElementPtrInst *GEPI) {
  auto nOperands = GEPI->getNumOperands();
  assert(nOperands <= 3);
  auto fatherType = GEPI->getSourceElementType();
  auto sonType = GEPI->getResultElementType();
  auto gepName = GEPI->hasName() ? GEPI->getName().str()
                                 : "gep." + itostr(NumInstrumentedGEPs);

  if (GEPI->getType()->isVectorTy()) {
    // NOTE: if loops are being vectorized, this will happen
    errs() << "[FSAN] WARNING: GEP with vector result type not handled, "
              "skipping instrumentation for this GEP: ";
    GEPI->print(errs());
    errs() << "\n";
    return;
  }
  IRBuilder<> IRB(GEPI->getNextNonDebugInstruction());

  Value *resultLong = IRB.CreatePointerCast(GEPI, IntptrTy);
  std::string endResultName = "";
  Value *taggedPointer = nullptr;
  bool isScalar = false;
  bool setMetadata = true;

  if (fatherType->isArrayTy()) {
    if (sonType->isAggregateType()) { /** GEP into array of aggregates */
      // NOTE: this should trigger whenever gepping into array of structs, and
      // array of arrays
      Value *untaggedResult = untagPointerIntrinsic(IRB, GEPI);
      taggedPointer = untaggedResult;
      endResultName = gepName + ".fsan.array.struct";
      // setMetadata = false;
    } // GEP into array of non-literal structs

    // else LEAVE THE PTR TAGGED!
    //
  } // GEP from array type
  else { /** father is not array */
    if (fatherType->isStructTy()) {
      StructType *ST = dyn_cast<StructType>(fatherType);
      if (ST && !ST->hasName()) {
        // UNNAMED STRUCT -> SKIP
        //
        // Clang emits hoisted struct representations for structs that result in
        // GEPs on anon structs on x86.
        // This probably introduces FNs.
        // errs() << " SKIPPING GEP ANON STRUCT ";
        // GEPI->print(errs());
        // errs() << "\n";
        return;
      }
      if (ST && ST->getName().str().find("union.") == 0) {
        // UNION SKIP
        // errs() << " SKIPPING GEP UNION ";
        // GEPI->print(errs());
        // errs() << "\n";
        auto *UnionNode = MDNode::get(
            *C, ConstantAsMetadata::get(ConstantInt::get(Int32Ty, 1)));
        // GEPI->setMetadata("fsan.noinstrument", UnionNode); // TODO
        return;
      }

      Value *sonTag = nullptr;
      auto sonIsScalar = !sonType->isStructTy() && !sonType->isVectorTy();
      bool sonIsArrayOfAggregates =
          sonType->isArrayTy() &&
          sonType->getArrayElementType()->isAggregateType();

      if (sonIsScalar) {
        // GEP struct -> scalar
        auto op2 = GEPI->getOperand(2);

        auto sonIdx = IRB.CreateAnd(
            IRB.CreateAdd(IRB.CreateZExtOrTrunc(GEPI->getOperand(2), IntptrTy),
                          ConstantInt::get(IntptrTy, 0x1Lu)),
            ConstantInt::get(IntptrTy, 0b1111UL)); // modulo 16
        Value *sonT =
            IRB.CreateAnd(sonIdx, ConstantInt::get(IntptrTy, 0b1111UL));
        // NOTE: tags might be 0 after this operation.
        // TODO: prevent nulltag
        sonTag = sonT;

        Value *untaggedResLong = untagPointer(IRB, resultLong);
        taggedPointer =
            tagPointer(IRB, GEPI->getType(), untaggedResLong, sonTag);
        endResultName = gepName + ".fsan.scalar";
        isScalar = true;
      } // GEP struct -> scalar
      else {
        if (sonType->isStructTy()) {
          Value *untaggedResult = untagPointerIntrinsic(IRB, GEPI);
          taggedPointer = untaggedResult;
          endResultName = gepName + ".fsan.struct";
          // setMetadata = false;
        } // son is a struct
        else if (sonIsArrayOfAggregates) {
          Value *untaggedResult = untagPointerIntrinsic(IRB, GEPI);
          taggedPointer = untaggedResult;
          endResultName = gepName + ".fsan.array.struct";
          // setMetadata = false;
        } // son is array of aggregates
      } // else - son is not scalar

    } // FATHER IS STRUCT
    else {
      // GEP type might be i8, i32, ptr etc.
      // NOTE: in these cases, we choose not to tag
      // NOTE: something fishy happens with vtables
      // errs() << "[FSAN] SKIPPING : GEP from UNK TYPE: ";
      // GEPI->print(errs());
      // errs() << "\n";
      return;
    }
  } // else - father is not an array

  if (!taggedPointer)
    return; // TODO: handle corner cases

  taggedPointer->setName(endResultName);
  auto *MD_node =
      MDNode::get(*C, ConstantAsMetadata::get(ConstantInt::get(Int32Ty, 1)));
  // if (setMetadata)
  //   dyn_cast<Instruction>(taggedPointer)
  //       ->setMetadata("fsan.instrument", MD_node);

  GEPI->replaceUsesWithIf(taggedPointer, [resultLong, GEPI, isScalar, sonType,
                                          setMetadata, MD_node](const Use &U) {
    auto *User = U.getUser();
    // TODO: I think this is BS
    bool isCallToMaskPtr = false;
    if (CallBase *CB = dyn_cast<CallBase>(User)) {
      if (CB->getCalledFunction() && CB->getCalledFunction()->hasName() &&
          CB->getCalledFunction()->getName().find("llvm.ptrmask") !=
              std::string::npos) {
        isCallToMaskPtr = true;
      }
    }

    bool safe =
        User != resultLong && !isa<LifetimeIntrinsic>(User) && !isCallToMaskPtr;
    if (isScalar) {
      // when used on a widened load, this produces FPs.
      // widened loads are produced right away by the FrontEnd
      // they are by-design FPs
      auto DL = GEPI->getModule()->getDataLayout();
      uint64_t fieldSize = DL.getTypeAllocSize(sonType);
      if (LoadInst *LI = dyn_cast<LoadInst>(User)) {
        // TODO: these have to be triaged
        auto loadSize = DL.getTypeAllocSize(LI->getType());
        if (loadSize > fieldSize) {
          errs() << "UNSAFE LOAD USER";
          LI->print(errs());
          errs() << "\n";
        }
        safe = safe && (fieldSize >= loadSize);
      } else if (PHINode *PHI = dyn_cast<PHINode>(User)) {
        // TODO: these have to be triaged
        auto PHIUsers = PHI->users();
        for (auto *PHIUser : PHIUsers) {
          if (LoadInst *LI = dyn_cast<LoadInst>(PHIUser)) {
            auto loadSize = DL.getTypeAllocSize(LI->getType());
            if (loadSize > fieldSize) {
              errs() << "UNSAFE LOAD USER";
              LI->print(errs());
              errs() << "\n";
            }
            safe = safe && (fieldSize >= loadSize);
          }
        }
      }
    }
    // if (safe && setMetadata) {
    //   GEPI->setMetadata("fsan.instrument", MD_node);
    // }
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
          errs() << "\t\tSTRUCT TYPE : " << typeName << "\n";
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
          // errs() << "\t\t UNION TYPE: " << baseType->getName().str() << "\n";
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
  bool isGVArray = GV->getValueType()->isArrayTy();
  Constant *Initializer = GV->getInitializer();
  Type *type = GV->getValueType(); // this is a lie!
  // errs() << "[FSAN] Instrumenting global variable: " << GV->getName()
  //        << ", type: " << *type << "\n";
  // std::string TypeStr;
  // raw_string_ostream RSO(TypeStr);
  // type->print(RSO);
  // errs() << "[FSAN] Type: " << RSO.str() << ", isVector: " <<
  // type->isVectorTy() << ", isArray: " << type->isArrayTy() << ", isStruct: "
  // << type->isStructTy() << ", is GVARRAY: " << isGVArray << "\n";

  assert(type->isAggregateType() &&
         "[FSAN] Expected only aggregate types to be instrumented");
  StructType *TYPE = nullptr;
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
  bool is3DMatrixOfStructs =
      type->isArrayTy() &&
      dyn_cast<ArrayType>(type)->getElementType()->isArrayTy() &&
      dyn_cast<ArrayType>(dyn_cast<ArrayType>(type)->getElementType())
          ->getElementType()
          ->isArrayTy() &&
      dyn_cast<ArrayType>(
          dyn_cast<ArrayType>(dyn_cast<ArrayType>(type)->getElementType())
              ->getElementType())
          ->getElementType()
          ->isStructTy();

  if (!(isStruct || isArrayOfStructs || isMatrixOfStructs ||
        is3DMatrixOfStructs)) {
    // TODO: refactor
    // errs() << "[FieldArmor - WARNING] Skipping global variable: "
    //        << GV->getName() << ", initializer type: " << *type << "\n";
    return;
  }

  bool isUnion = false; // is union or aggregates of unions
  std::string struct_name = "";

  if (type->isStructTy()) {
    StructType *ST = dyn_cast<StructType>(type);
    if (ST->isLiteral()) {
      int depth = 0;
      // something is rotten in the state of denmark!
      // DEPTH can be GT 1 because const struct arrays become structs of the
      // same type!!!!
      auto *tmp = getStructTypeFromDbgInfo(GV, &depth, &isUnion);

      if (tmp) {
        ST = tmp;
        // errs() << "BOOM got NON NESTED struct type from dbg info: "
        //        << ST->getName() << " BUT DEPTH " << depth << "\n";
        if (depth != 0) {
          // errs() << "[FieldArmor - WARNING] SKIPPING THIS CRAP!\n";
          return;
        }
      } else
        return;
    }
    isUnion = ST->getName().str().find("union.") != std::string::npos;
    struct_name = ST->getName().str();
    TYPE = ST;
  }

  if (isArrayOfStructs) {
    Type *elementType = type->getArrayElementType();
    StructType *STA = dyn_cast<StructType>(elementType);

    // errs() << "[FSAN] Instrumenting global variable with array of "
    //           "structs: "
    //        << GV->getName() << "\n";
    if (STA->isLiteral()) {
      auto *tmp = getStructTypeFromDbgInfo(GV, nullptr, &isUnion);
      if (tmp) {
        STA = tmp;
        // errs() << "BOOM got struct type from dbg info: " << STA->getName()
        //        << "\n";
      }

      else
        return;
    }
    isUnion = STA->getName().str().find("union.") != std::string::npos;
    struct_name = STA->getName().str();
    TYPE = STA;
  }

  if (isMatrixOfStructs) {
    Type *elementType = dyn_cast<ArrayType>(type)->getElementType();
    Type *structType = dyn_cast<ArrayType>(elementType)->getElementType();
    StructType *STM = dyn_cast<StructType>(structType);
    // errs() << "[FSAN] Instrumenting global variable with matrix of "
    //           "structs: "
    //        << GV->getName() << "\n";
    if (STM->isLiteral()) {
      auto *tmp = getStructTypeFromDbgInfo(GV, nullptr, &isUnion);
      if (tmp) {
        // errs() << "BOOM got struct type from dbg info: " << STM->getName()
        //        << "\n";
        STM = tmp;
      }

      else
        return;
    }
    isUnion = STM->getName().str().find("union.") != std::string::npos;
    struct_name = STM->getName().str();
    TYPE = STM;
  }

  if (is3DMatrixOfStructs) {
    // errs() << "[FSAN] Instrumenting global 3D array of structs: "
    //        << GV->getName() << "\n";
    Type *elementType = dyn_cast<ArrayType>(type)->getElementType();
    Type *innerArrayType = dyn_cast<ArrayType>(elementType)->getElementType();
    Type *structType = dyn_cast<ArrayType>(innerArrayType)->getElementType();
    StructType *STM = dyn_cast<StructType>(structType);
    if (STM->isLiteral()) {
      auto *tmp = getStructTypeFromDbgInfo(GV, nullptr, &isUnion);
      if (tmp) {
        STM = tmp;
      }

      else
        return;
    }
    isUnion = STM->getName().str().find("union.") != std::string::npos;
    struct_name = STM->getName().str();
    TYPE = STM;
  }

  if (isUnion) {
    // errs() << "[FSAN] Skipping union/aggregate of unions GV: "
    //        << GV->getName() << "\n";
    return;
  }

  uint64_t SizeInBytes =
      M.getDataLayout().getTypeAllocSize(Initializer->getType());

  // errs() << "[FSAN] Instrumenting global variable: " << GV->getName()
  //        << ", is array: " << isGVArray << "\n";
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

    assert(!struct_name.empty() &&
           "Struct name must be valid to instrument global variable.");

    auto *TagVector =
        M.getGlobalVariable(struct_name + ".fieldarmor.tagvec", true);

    if (TagVector == nullptr) {
      // TODO: create and then fail if still no TV
      createTagVector(TYPE);
      TagVector = M.getGlobalVariable(struct_name + ".fieldarmor.tagvec", true);
      // NOTE: this fails for arrays of pairs
      // errs() << "[FSAN] Error: Tag vector global not found for struct:
      // "
      //        << struct_name << "\n";
      // errs() << *GV << "\n";
      // errs() << *type << "\n";
      // errs() << "isStructTy()? " << type->isStructTy() << "\n";
      // errs() << "isArrayTy()? " << type->isArrayTy() << "\n";
      // errs() << "isMatrixOfStructs? " << isMatrixOfStructs << "\n";
      // errs() << "isArrayOfStructs? " << isArrayOfStructs << "\n";
      // errs() << "isLiteral? "
      //        << (type->isStructTy() ? dyn_cast<StructType>(type)->isLiteral()
      //                               : false)
      //        << "\n";
      // errs() << "isOpaque? "
      //        << (type->isStructTy() ? dyn_cast<StructType>(type)->isOpaque()
      //                               : false)
      //        << "\n";
      // errs() << "isSized?"
      //        << (type->isStructTy() ? dyn_cast<StructType>(type)->isSized()
      //                               : false)
      //        << "\n";
      assert(TagVector &&
             "Tag vector global must exist and be properly initialized.");
    }
    auto *TVRelPtr = ConstantExpr::getTrunc(
        ConstantExpr::getSub(ConstantExpr::getPtrToInt(TagVector, Int64Ty),
                             ConstantExpr::getPtrToInt(Descriptor, Int64Ty)),
        Int32Ty);
    Constant *arraySize = nullptr;
    if (isStruct) {
      // single struct
      arraySize = ConstantInt::get(Int32Ty, 0x1);
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
      } else if (is3DMatrixOfStructs) {
        auto outerArrayType = dyn_cast<ArrayType>(type);
        auto middleArrayType =
            dyn_cast<ArrayType>(outerArrayType->getElementType());
        auto innerArrayType =
            dyn_cast<ArrayType>(middleArrayType->getElementType());
        assert(outerArrayType &&
               "Outer array type must be valid for 3D matrix of structs.");
        assert(middleArrayType &&
               "Middle array type must be valid for 3D matrix of structs.");
        assert(innerArrayType &&
               "Inner array type must be valid for 3D matrix of structs.");

        arraySize =
            ConstantInt::get(Int32Ty, outerArrayType->getNumElements() *
                                          middleArrayType->getNumElements() *
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
  // in the asm, this gets evaluated to 2^^32. The linker, subsequently,
  // does the relocation magic and replaces that with something else like
  // the thing down here
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
          errs() << "[FSan] global variable (3D array): " << GV.getName()
                 << "\n";
          // continue; // TODO: no longer skip, correctly engineer
        } // arrays of arrays of something other than structs
        else if (elemArrayType->getElementType()->isStructTy()) {
          // bool isLiteral =
          // dyn_cast<StructType>(elemArrayType->getElementType())
          //                      ->isLiteral();
          // if (isLiteral)
          //   LiteralStructs++;
          bool isUnion =
              // isLiteral ? true
              // :
              dyn_cast<StructType>(elemArrayType->getElementType())
                  ->getName()
                  .str()
                  .find("union.") == 0;
          if (isUnion) { // || isLiteral) {
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
  //   // Fuchsia is always PIE, which means that the beginning of the
  //   address
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
    // errs() << "[FSAN] Tag vector " << TagVecName
    //        << " already exists, skipping creation.\n";
    return;
  }
  auto size = M.getDataLayout().getTypeAllocSize(t);

  u_int8_t *tags = nullptr;
  bool isLiteral = t->isLiteral();
  // if (isLiteral) {
  //   LiteralStructs++;
  //   // errs() << "[FSAN] StructType " << *t << " is literal!\n";
  // }

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
  // errs() << "[FSAN] Created tag vector " << TagVecName << "\n";
  NumDefinedTagVectors++;
}

void HWAddressSanitizer::createTagVectors() {
  auto identifiedStructTypes = M.getIdentifiedStructTypes();
  for (auto t : identifiedStructTypes)
    // errs() << "[FSAN] Identified StructType: " << *t << ", is literal
    // "
    //        << (t->isLiteral() ? "yes" : "no") << "\n";

    for (auto t : identifiedStructTypes) {
      StructType *ty = dyn_cast<StructType>(t);
      // errs() << "[FSAN] Creating tag vector for StructType " << *t <<
      // "\n";
      /** NOTE: opaque types are not sized. */
      if (!ty->isSized()) {
        // Q: what is the solution to this?
        // errs() << "[FSAN] StructType " << *t << " is not sized!\n";
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
  // Ty->dump();
  memset(tags, 0xff, DL.getTypeAllocSize(Ty)); // padding is gonna stay tagged!

  assert(tags && "Could not allocate tags array");
  std::deque<std::tuple<Type *, uint8_t, uint8_t, uint8_t, size_t>> AggQueue;

  auto levelZeroFieldsOffsets = DL.getStructLayout(Ty)->getMemberOffsets();

  uint8_t fatherT = 0;
  uint8_t fatherL = 0;
  uint16_t sonIdx = 1; // NOTE: 2^^16 max number of fields because tag on 4 bits
  if (levelZeroFieldsOffsets.size() >= (1 << 16) - 1) {
    /** Too many fields :( */
    errs() << "[FSAN] Struct " << *Ty
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
    if (isLitStr)
      LiteralStructs++;
    auto isUnion =
        ST_son && !isLitStr && (ST_son->getName().find("union.") == 0);
    // auto isClass = ST_son && !isLitStr && !isUnion &&
    //                (ST_son->getName().find("class.") == 0);
    // TODO: if a class is embedded in a struct and the class has padding in
    // the end, that is treated as an extra field and can lead to FPs? This
    // has never happened till now.
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
      if (StructType *structType = dyn_cast<StructType>(elementType)) {
        // case : ARRAY of STRUCTS embedded in a struct

        if (structType->isLiteral()) {
          LiteralStructs++;
          // dont tag literal structs arrays for now
          continue;
        } else if (structType->getName().str().find("union.") == 0) {
          // dont tag union arrays for now
          continue;
        }

        auto structName = structType->getStructName().str();
        auto tagVectorGlobal =
            M.getGlobalVariable(structName + ".fieldarmor.tagvec", true);

        if (!tagVectorGlobal)
          createTagVector(structType);

        tagVectorGlobal =
            M.getGlobalVariable(structName + ".fieldarmor.tagvec", true);

        if (!tagVectorGlobal) {
          // continue;
          assert(tagVectorGlobal &&
                 "computeTags - error in creating and retrieving TV");
        }

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
        // 2+d matrix
        auto innerArrayType = dyn_cast<ArrayType>(elementType);
        Type *innerElementType = innerArrayType->getArrayElementType();
        if (innerElementType->isStructTy()) {
          // case : matrix of structs
          auto structType = cast<StructType>(innerElementType);
          if (structType->isLiteral()) {
            // dont tag literal struct matrices for now
            LiteralStructs++;
            continue;
          } else if (structType->getName().str().find("union.") == 0) {
            // dont tag union matrices for now
            continue;
          }

          // TODO: handle arrays of C++ classes. What happens if the wrong
          // tag vector is used? E.g. base vs non-base? Using struct size
          // should be fine though.

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
        else if (innerElementType->isArrayTy()) {
          // case : matrix of arrays -> if struct, tag it. If not struct, no
          // tags.
          auto thirdLevElementType =
              dyn_cast<ArrayType>(innerElementType)->getArrayElementType();
          if (thirdLevElementType->isStructTy()) {
            // case : 3D matrix of structs
            auto structType = cast<StructType>(thirdLevElementType);
            if (structType->isLiteral()) {
              LiteralStructs++;
              // dont tag literal struct matrices for now
              continue;
            } else if (structType->getName().str().find("union.") == 0) {
              // dont tag union matrices for now
              continue;
            }

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
            // compute the total number of structs enclosed in this
            // aggregate
            auto *L1arrayType = dyn_cast<ArrayType>(sonType);
            auto *L2arrayType =
                dyn_cast<ArrayType>(L1arrayType->getElementType());
            auto *L3arrayType =
                dyn_cast<ArrayType>(L2arrayType->getElementType());
            structType =
                dyn_cast<StructType>(L3arrayType->getArrayElementType());
            assert(structType &&
                   "Expected struct as innermost element of 3D matrix");
            errs() << "3D array of " << structType->getStructName() << "\n";
            auto L1Els = L1arrayType->getNumElements();
            auto L2Els = L2arrayType->getNumElements();
            auto L3Els = L3arrayType->getNumElements();
            auto L1ArraySize = DL.getTypeAllocSize(L1arrayType);
            auto L2ArraySize = DL.getTypeAllocSize(L2arrayType);
            auto L3ArraySize = DL.getTypeAllocSize(L3arrayType);

            auto structSize = DL.getTypeAllocSize(structType);
            auto L1Offset = sonOffset; // offset from the beginning of the
                                       // struct of the outermost array
            for (u_int64_t L1 = 0; L1 < L1Els; L1++) {
              // each element is an array of structs
              L1Offset += L1 * L2ArraySize;

              for (u_int64_t L2 = 0; L2 < L2Els; L2++) {
                uint64_t L2Offset = L1Offset + L2 * L3ArraySize;

                for (u_int64_t L3 = 0; L3 < L3Els; L3++) {
                  uint64_t L3Offset = L2Offset + L3 * structSize;

                  for (u_int64_t i = 0; i < structSize; i++) {
                    tags[L3Offset + i] = static_cast<uint8_t>(
                        cast<ConstantInt>(tagVectorInit->getAggregateElement(i))
                            ->getZExtValue());
                  }
                } // for each struct in the innermost array
              } // for each array of structs
            } // for each matrix of structs
            errs() << "TAGGED 3D MATRIX OF STRUCTS\n";
          } // 3D matrix of structs
          else {
            // 3+D array of something that is not a struct -> dont tag! Memset
            // to 0!
            // TODO! This could bring FPs, debug!
            uint8_t sonT = (fatherT + sonIdx) % 16;
            uint8_t sonTag = sonT | (fatherL << 4);
            uint64_t sonSize = DL.getTypeAllocSize(sonType);
            for (uint64_t i = 0; i < sonSize; i++) {
              tags[sonOffset + i] = sonTag;
            }
          }
        }

        else {
          // 2D matrices of scalars ONLY.
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
        uint64_t sonSize =
            DL.getTypeAllocSize(sonType); // USE ARRAY SIZE INSTEAD
        uint64_t nElems = dyn_cast<ArrayType>(sonType)->getNumElements();
        uint64_t remainingSizeOfStruct = DL.getTypeAllocSize(Ty) - (sonOffset);
        bool isLastFieldOfStruct =
            (sonIdx) ==
            Ty->getNumContainedTypes(); // NOTEL sonIdx is adj to be 1-based
        if (nElems == 1 && isLastFieldOfStruct) {
          errs() << "[FSAN] Detected possible flexible array at offset "
                 << sonOffset << " of struct " << *Ty << ", memsetting "
                 << remainingSizeOfStruct << " bytes to 0\n";
          memset(&tags[sonOffset], 0x00, remainingSizeOfStruct);

        } else
          for (uint64_t i = 0; i < sonSize; i++)
            tags[sonOffset + i] = sonTag;
      } // array of scalars
    } // case: son is array

    else {
      // case : scalar fields, literal structs, unions == ALL SCALAR

      if (sonType->isStructTy()) {
        StructType *ty = dyn_cast<StructType>(sonType);
        // errs() << "[DBG] Embedded struct is a literal " << *sonType << "\n";
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
