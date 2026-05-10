/** This file is part of custom HWAsan - FSAN */
#include "llvm/Transforms/Instrumentation/RuntimeTaggingSupport.hpp"
#include "llvm/Demangle/Demangle.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Format.h"
#include <fstream>
static cl::opt<bool> clFSAN_FAM(
    "fsan-fam",
    cl::desc("clear padding at the end of a struct in the presence of FAM"),
    cl::Hidden, cl::init(true));

static cl::opt<std::string> clFSAN_BLOCKLIST_TAG_FILEPATH(
    "fsan-blocklist-tag-filepath",
    cl::desc("Path to the blocklist tag file, which contains struct names to "
             "blocklist from tagging"),
    cl::Hidden, cl::init(""));

namespace RuntimeTaggingSupport {
#define TAG_MAX 64
#define LEVEL_SHIFT 6 // DEBUG

__attribute__((noinline)) void createTagVector(StructType *ST, Module &M) {
  auto *Int8Ty = Type::getInt8Ty(M.getContext());

  std::string TagVecName = ST->getStructName().str() + ".fieldarmor.tagvec";
  auto *TagVec = M.getGlobalVariable(TagVecName, true);
  if (TagVec)
    return;

  auto Size = M.getDataLayout().getTypeAllocSize(ST);

  u_int8_t *Tags = nullptr;
  bool isLiteral = ST->isLiteral();

  bool isUnion =
      !isLiteral && ST->getName().str().find("union.") != std::string::npos;
  auto demangledTypeName = demangle(ST->getStructName().str());

  if (isLiteral || isUnion) {
    // literal, unions == all 0 tags
    // errs() << "[FSAN - TAG] NULL TAG ON STRUCT " << *ST
    //        << " (literal: " << isLiteral << ", union: " << isUnion << ")\n";
    Tags = new u_int8_t[Size];
    memset(Tags, (unsigned char)0x00, Size);
  } else if (!clFSAN_BLOCKLIST_TAG_FILEPATH.getValue().empty()) {
    std::ifstream BlocklistFile(clFSAN_BLOCKLIST_TAG_FILEPATH.getValue());
    if (BlocklistFile.is_open()) {
      std::string Line;
      while (std::getline(BlocklistFile, Line)) {
        // NOTE: we want to match struct.sockaddr, but not struct.sockaddr_in
        // errs() << "[FSAN - TAG] N: " << demangledTypeName << " VS: " << Line
        // << "\n";
        auto LenLine = Line.length();
        auto LenType = demangledTypeName.length();
        bool containsAsterisk = Line.find('*') != std::string::npos;
        if (containsAsterisk) {
          // if the line contains an asterisk, we check if the demangled type
          // name contains the line without the asterisk
          auto LineWithoutAsterisk = Line;
          LineWithoutAsterisk.erase(std::remove(LineWithoutAsterisk.begin(),
                                                LineWithoutAsterisk.end(), '*'),
                                    LineWithoutAsterisk.end());
          if (demangledTypeName.find(LineWithoutAsterisk) !=
              std::string::npos) {
            Tags = new u_int8_t[Size];
            memset(Tags, (unsigned char)0x00, Size);
            errs() << "N:" << demangledTypeName << " VS:" << Line << "\n";
            errs() << "[FSAN - TAG] NULL TAG ON STRUCT " << *ST
                   << " (blocklisted by pattern: " << Line << ")\n";
            break;
          }
        } else if (demangledTypeName.find(Line) == 0) {
          Tags = new u_int8_t[Size];
          memset(Tags, (unsigned char)0x00, Size);
          errs() << "N:" << demangledTypeName << " VS:" << Line << "\n";
          errs() << "[FSAN - TAG] NULL TAG ON STRUCT " << *ST
                 << " (blocklisted by pattern: " << Line << ")\n";
          break;
        }
      }
    }
  }

  // if at the end of the checks, no Tags, then compute
  if (!Tags)
    Tags = ComputeTags(ST, M);

  assert(Tags && "Tags array must be valid after computation.");

  ArrayType *TagArrayType = ArrayType::get(Int8Ty, Size);
  std::vector<llvm::Constant *> Elements(Size,
                                         llvm::ConstantInt::get(Int8Ty, 0));
  for (unsigned long i = 0; i < Size; i++) {
    Elements[i] = llvm::ConstantInt::get(Int8Ty, Tags[i]);
  }
  delete[] Tags; // NOTE: is it responsibility of the caller to delete

  llvm::Constant *Init = llvm::ConstantArray::get(TagArrayType, Elements);
  auto *NewlyCreatedTVGV = new GlobalVariable(
      M, TagArrayType, true, GlobalVariable::PrivateLinkage, Init, TagVecName);
  NewlyCreatedTVGV->setSection(".data");
  appendToCompilerUsed(M, NewlyCreatedTVGV);
}

__attribute__((noinline)) Value *RetrieveOrCreateTagVector(StructType *ST,
                                                           Module &M) {
  auto *TagVector = M.getGlobalVariable(
      ST->getStructName().str() + ".fieldarmor.tagvec", true);
  if (!TagVector) {
    createTagVector(ST, M);
    TagVector = M.getGlobalVariable(
        ST->getStructName().str() + ".fieldarmor.tagvec", true);
  }
  return TagVector;
}

__attribute__((noinline)) u_int8_t *ComputeTags(StructType *Ty, Module &M) {
  // TODO: remove the 0 tag from everywhere else
  DataLayout DL = M.getDataLayout();
  u_int8_t *Tags = new u_int8_t[DL.getTypeAllocSize(Ty)];
  assert(Tags && "Could not allocate Tags array");
  const u_int8_t PaddingTag = 0xff;

  // NOTE: initialize to padding tag so that padding is already tagged
  memset(Tags, PaddingTag, DL.getTypeAllocSize(Ty));

  std::deque<std::tuple<Type *, uint8_t, uint8_t, uint8_t, size_t>> AggQueue;
  auto FieldsOffsets = DL.getStructLayout(Ty)->getMemberOffsets();

  uint8_t fatherT = 0;
  uint8_t fatherL = 0;
  uint16_t sonIdx = 1;
  // NOTE: 2^^16 max number of fields
  if (FieldsOffsets.size() >= (1 << 16) - 1) {
    /** Too many fields :( */
    errs() << "[FSAN - TAG] Struct " << *Ty
           << " has too many fields to be tagged properly.\n";
    assert(false && "Struct has too many fields to be tagged properly.");
  }

  for (auto *Sty : Ty->subtypes()) {
    AggQueue.push_back(std::make_tuple(Sty, fatherT, fatherL, sonIdx,
                                       FieldsOffsets[sonIdx - 1]));
    sonIdx++;
  }

  while (!AggQueue.empty()) {

    auto Tuple = AggQueue.front();
    AggQueue.pop_front();
    sonIdx = std::get<3>(Tuple);
    Type *CurFieldType = std::get<0>(Tuple);
    fatherT = std::get<1>(Tuple);
    fatherL = std::get<2>(Tuple);
    size_t CurFieldOffset = std::get<4>(Tuple);

    auto *CurFieldStructType = dyn_cast<StructType>(CurFieldType);
    auto CurFieldIsLiteral =
        CurFieldStructType && CurFieldStructType->isLiteral();
    auto CurFieldIsUnion = CurFieldStructType && !CurFieldIsLiteral &&
                           (CurFieldStructType->getName().find("union.") == 0);

    if (CurFieldStructType && !CurFieldIsLiteral && !CurFieldIsUnion) {
      uint8_t Count = 0;
      auto ContainedSubTypes = CurFieldType->getNumContainedTypes();

      auto ContainedSubTyOffsets =
          DL.getStructLayout(cast<StructType>(CurFieldType))
              ->getMemberOffsets();
      size_t CurContainedSubTy = 0;

      for (Type *SSty : llvm::reverse(CurFieldType->subtypes())) {
        CurContainedSubTy =
            ContainedSubTyOffsets[ContainedSubTypes - Count - 1] +
            CurFieldOffset;
        AggQueue.push_front(std::make_tuple(SSty, 0, (fatherL + 1) % 4,
                                            ContainedSubTypes - Count,
                                            CurContainedSubTy));
        Count++;
      } // for subtype
    } // if son struct

    else if (CurFieldType->isArrayTy()) {
      // NOTE: depth 4 is arbitrary
      const int MaxDepth = 12;
      int CurDepth = 1;

      auto *CurArrayType = dyn_cast<ArrayType>(CurFieldType);
      u_int64_t Elements = CurArrayType->getNumElements();
      auto *ElemType = CurArrayType->getArrayElementType();

      while (ElemType->isArrayTy() && CurDepth <= MaxDepth) {
        CurArrayType = dyn_cast<ArrayType>(ElemType);
        ElemType = CurArrayType->getArrayElementType();
        Elements *= CurArrayType->getNumElements();
        CurDepth++;
      }

      // check type
      if (ElemType->isStructTy()) {
        // retrieve or create tag vector for struct type
        auto *ElemStructType = dyn_cast<StructType>(ElemType);
        size_t ElemStructSize = DL.getTypeAllocSize(ElemStructType);
        auto *TagVector = RetrieveOrCreateTagVector(ElemStructType, M);
        assert(TagVector && "Failed to retrieve or create tag vector for "
                            "struct element type.");
        GlobalVariable *TVGV = dyn_cast<GlobalVariable>(TagVector);

        auto *TVInit = cast<Constant>(TVGV->getInitializer());
        assert(TagVector &&
               "Tag vector must be valid for struct element type.");
        for (uint64_t K = 0; K < Elements; K++) {
          size_t ElemOffset = CurFieldOffset + K * ElemStructSize;
          for (size_t H = 0; H < ElemStructSize; H++) {
            auto *ElemTag = cast<ConstantInt>(TVInit->getAggregateElement(H));
            assert(ElemTag &&
                   "Element tag must be a constant integer in the tag vector.");
            auto ElemTagValue = ElemTag->getZExtValue();
            assert(ElemTagValue <= 0xff &&
                   "Element tag value must fit in a byte.");
            Tags[ElemOffset + H] = static_cast<uint8_t>(ElemTagValue);
          }
        }

      } else {
        // scalar arrays get the same tag
        // NOTE: this case catches arrays with depth > MAX_DEPTH as well
        auto Tag = (sonIdx) % TAG_MAX; //  | (fatherL << 4);
        if (Tag == 0) {
          Tag = 1;
        }
        size_t ArraySize = DL.getTypeAllocSize(CurFieldType);

        memset(&Tags[CurFieldOffset], Tag, ArraySize);

        auto *arrTy = dyn_cast<ArrayType>(CurFieldType);
        auto ArrayFieldElems = arrTy->getNumElements();

        // NOTE: this does not violate the C std!
        // ONLY ENABLE IF IT'S FULL OF THESE BUGS AND THEY ARE ANNOYING FOR
        // FUZZING
        bool IsLastField = sonIdx == FieldsOffsets.size();
        if (IsLastField) {
          // || ArrayFieldElems == 1
          // NOTE: the field might overlap with compiler-inserted padding
          // TODO:double check that this makes sense in STD
          if (ArrayFieldElems == 0 || !clFSAN_FAM) {
            errs() << "[FSAN - TAG] FLEX MEMBER IN " << *Ty << "\n";
            auto RemainderBytes = DL.getTypeAllocSize(Ty) - CurFieldOffset;
            if (clFSAN_FAM)
              memset(&Tags[CurFieldOffset], 0x00, RemainderBytes);
          }
          // FFMPEG fix: remove FPs untagging artifically padded structs? Can
          // be patched in SRC
        } // if LastField
      }
    } // cur sub field is array

    else {
      // case : scalar fields, literal structs, unions == ALL SCALAR
      if (CurFieldType->isStructTy() || CurFieldIsLiteral || CurFieldIsUnion) {
        // union, literal
        memset(&Tags[CurFieldOffset], 0x00, DL.getTypeAllocSize(CurFieldType));
      } else {
        // scalar field
        uint8_t CurFieldT = (sonIdx) % TAG_MAX;
        if (CurFieldT == 0) {
          CurFieldT = 1; // avoid 0 tag for scalar fields, which is the
                         // default tag for padding and unions/literal structs
        }
        uint8_t CurFieldTag = CurFieldT; // | (fatherL << 4);
        int CurFieldSize = DL.getTypeAllocSize(CurFieldType);
        memset(&Tags[CurFieldOffset], CurFieldTag, CurFieldSize);
      }
    } // case : scalar fields, literal structs, unions
  } // while agg queue not empty
  // DEBUG
  // errs() << "TV for type " << *Ty << ": ";
  // for (size_t i = 0; i < DL.getTypeAllocSize(Ty); i++) {
  //   errs() << llvm::format_hex(Tags[i], 2);
  // }
  // errs() << "\n";
  return Tags;
} // ComputeTags

} // namespace RuntimeTaggingSupport