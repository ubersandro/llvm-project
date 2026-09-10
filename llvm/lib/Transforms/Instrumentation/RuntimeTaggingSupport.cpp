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
static cl::opt<bool> clFSAN_SKIP_ANON_STRUCTS(
    "fsan-skip-anon-structs",
    cl::desc("Skip tagging anonymous structs and classes (i.e., those whose "
             "name starts with struct.anon or class.anon)"),
    cl::Hidden, cl::init(false));

static cl::opt<bool> clFSAN_DEPTH_AWARE_TAGGING(
    "fsan-depth-aware-tagging",
    cl::desc("Enable depth-aware tagging for nested structures"), cl::Hidden,
    cl::init(false));
namespace RuntimeTaggingSupport {
uint64_t TAG_SPACE = 6ULL;
uint64_t T_MAX = (1ULL << (TAG_SPACE-1ULL)); // 0b100000

__attribute__((noinline)) void createTagVector(Type *TY, Module &M, int depth) {
  auto *Int8Ty = Type::getInt8Ty(M.getContext());
  auto DL = M.getDataLayout();
  uint64_t Size = DL.getTypeAllocSize(TY);

  u_int8_t *Tags = new u_int8_t[Size];
  assert(Tags && "Failed to allocate memory for Tags array");
  bool TagsInited = false;
  Value *TagVec = nullptr;
  std::string TagVecName;

  if (StructType *ST = dyn_cast<StructType>(TY)) {
    TagVecName = ST->getStructName().str() + ".fieldarmor.tagvec.depth" +
                 std::to_string(depth);
    TagVec = M.getGlobalVariable(TagVecName, true);
    if (TagVec) {
      delete[] Tags;
      return;
    }

    bool isLiteral = ST->isLiteral();

    bool isUnion =
        !isLiteral && ST->getName().str().find("union.") != std::string::npos;
    auto isAnonStructOrClass = ST->getName().str().find("struct.anon") == 0 ||
                               ST->getName().str().find("class.anon") == 0;
    bool SkipAnonStruct = isAnonStructOrClass && clFSAN_SKIP_ANON_STRUCTS;
    if (SkipAnonStruct)
      errs() << "[FSAN - TAG] Skipping anonymous struct " << *ST << "\n";
    auto demangledTypeName = demangle(ST->getStructName().str());

    if (isLiteral || isUnion || SkipAnonStruct) {
      memset(Tags, (unsigned char)0x00, Size);
      TagsInited = true;
    } else if (!clFSAN_BLOCKLIST_TAG_FILEPATH.getValue().empty()) {
      std::ifstream BlocklistFile(clFSAN_BLOCKLIST_TAG_FILEPATH.getValue());
      if (BlocklistFile.is_open()) {
        std::string Line;
        // TODO: add support for selectively blocklisting specific fields using
        // indexes, not names
        while (std::getline(BlocklistFile, Line)) {
          // if it's emtpy line, skip

          if (Line.empty())
            continue;
          // if line len <= 1 skip
          if (Line.length() <= 1)
            continue;
          // NOTE: we want to match struct.sockaddr, but not struct.sockaddr_in
          bool containsAsterisk = Line.find('*') != std::string::npos;
          if (containsAsterisk) {
            // if the line contains an asterisk, we check if the demangled type
            // name contains the line without the asterisk
            auto LineWithoutAsterisk = Line;
            LineWithoutAsterisk.erase(std::remove(LineWithoutAsterisk.begin(),
                                                  LineWithoutAsterisk.end(),
                                                  '*'),
                                      LineWithoutAsterisk.end());
            if (demangledTypeName.find(LineWithoutAsterisk) !=
                std::string::npos) {
              memset(Tags, (unsigned char)0x00, Size);
              TagsInited = true;
              errs() << "[FSAN - TAG] NULL TAG ON STRUCT " << *ST
                     << " (matched blocklist line: " << Line << ")\n";
              break;
            }
          } else if (demangledTypeName.find(Line) == 0) {
            memset(Tags, (unsigned char)0x00, Size);
            TagsInited = true;
            errs() << "[FSAN - TAG] NULL TAG ON STRUCT " << *ST
                   << " (matched blocklist line: " << Line << ")\n";
            break;
          }
        }
      }
    }

    // if at the end of the checks, no Tags, then compute
    if (!TagsInited) {
      Tags = ComputeTags(ST, M, depth, Tags);
      TagsInited = true;
    }
  } // if Stuct
  else if (ArrayType *AT = dyn_cast<ArrayType>(TY)) {
    depth = 0;
    std::string ArrayName;
    raw_string_ostream OS(ArrayName);
    AT->print(OS);

    TagVecName = ArrayName + ".tagvec.depth" + std::to_string(depth);
    TagVec = M.getGlobalVariable(TagVecName, true);
    if (TagVec) {
      delete[] Tags;
      return;
    }
    // compute it if not available
    memset(Tags, (unsigned char)0x00, Size);
    ComputeTagsOnNDArray(AT, M, DL, 0, Tags, 0);
    TagsInited = true;
  } // if Array
  else {
    delete[] Tags;
    return;
  }
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

__attribute__((noinline)) Value *RetrieveOrCreateTagVector(Type *TY, Module &M,
                                                           int depth) {
  Value *TagVector = nullptr;

  if (StructType *ST = dyn_cast<StructType>(TY)) {
    // base sol 1: 1 tag vec for each level of nesting of a structure
    auto TagVecName = ST->getStructName().str() + ".fieldarmor.tagvec.depth" +
                      std::to_string(depth);

    TagVector = M.getGlobalVariable(TagVecName, true);
    if (!TagVector) {
      createTagVector(ST, M, depth);
      TagVector = M.getGlobalVariable(TagVecName, true);
    }
  } else if (ArrayType *AT = dyn_cast<ArrayType>(TY)) {
    depth = 0;
    std::string ArrayName;
    raw_string_ostream OS(ArrayName);
    AT->print(OS);
    TagVector = M.getGlobalVariable(
        ArrayName + ".tagvec.depth" + std::to_string(depth), true);
    if (!TagVector) {
      createTagVector(AT, M, 0); // TODO depth later
      TagVector = M.getGlobalVariable(
          ArrayName + ".tagvec.depth" + std::to_string(depth), true);
    }
  }
  return TagVector;
}
__attribute__((noinline)) void ComputeTagsOnNDArray(ArrayType *Ty, Module &M,
                                                    const DataLayout &DL,
                                                    int depth, u_int8_t *Tags,
                                                    uint64_t BaseOffset) {
  // TODO: establish S bit at the end, adapting L bits accordingly
  std::deque<std::tuple<Type * /*EL*/, uint64_t /*L_TMP*/,
                        uint64_t /*offset inside tag vector*/,
                        uint64_t /*cur dim */, uint64_t /*cur arr idx */>>
      Stack;
  // auto ArrayDims = depth;
  auto ArrayDims = 1;
  ArrayType *CurArrayTy = Ty;
  while (CurArrayTy->getArrayElementType()->isArrayTy()) {
    CurArrayTy = dyn_cast<ArrayType>(CurArrayTy->getArrayElementType());
    ArrayDims++;
  }

  for (uint64_t idx = 0; idx < Ty->getNumElements(); idx++) {
    auto el = Ty->getElementType();
    auto Offset = BaseOffset + idx * DL.getTypeAllocSize(el);
    uint64_t T_TMP = -1;
    uint64_t bit = idx % 2;
    T_TMP = 1ULL << 5;
    Stack.push_back(std::make_tuple(el, T_TMP, Offset, ArrayDims - 1, idx));
  }

  while (!Stack.empty()) {
    auto [EL, T_TMP, Offset, Depth, IDX] = Stack.back();
    Stack.pop_back();

    if (EL->isArrayTy()) {
      auto *ArrTy = dyn_cast<ArrayType>(EL);
      auto *ElemTy = ArrTy->getArrayElementType();
      uint64_t NumElems = ArrTy->getNumElements();

      for (uint64_t idx = 0; idx < NumElems; idx++) {
        uint64_t T_TMP_NEW = T_TMP | ((IDX % 2) << (Depth - 1));
        Stack.push_back(std::make_tuple(
            ElemTy, T_TMP_NEW, Offset + idx * DL.getTypeAllocSize(ElemTy),
            Depth - 1, idx));
      } // for
    } // if element is array
    else {
      // arrays of depth 1 have same tag for all elems
      memset(&Tags[Offset], T_TMP, DL.getTypeAllocSize(EL));
    } // else
  }
} // ComputeTagsOnNDArray

__attribute__((noinline)) u_int8_t *ComputeTags(StructType *Ty, Module &M,
                                                int depth, uint8_t *Tags) {
  depth = 0; // NO L
  // TODO: remove the 0 tag from everywhere else
  DataLayout DL = M.getDataLayout();
  assert(Tags && "Could not allocate Tags array");
  const u_int8_t PaddingTag = 0xff;

  // NOTE: initialize to padding tag so that padding is already tagged
  memset(Tags, PaddingTag, DL.getTypeAllocSize(Ty));

  std::deque<std::tuple<Type *, uint8_t, int, uint64_t, uint64_t>> AggQueue;
  auto FieldsOffsets = DL.getStructLayout(Ty)->getMemberOffsets();

  uint8_t fatherT = 0; /* unused */
  int fatherL = 0; // NO L
  uint64_t sonIdx = 1;
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
    Type *CurFieldType = std::get<0>(Tuple);
    fatherT = std::get<1>(Tuple);
    // fatherL = std::get<2>(Tuple);
    fatherL = 0; // NO L
    sonIdx = std::get<3>(Tuple);
    uint64_t CurFieldOffset = std::get<4>(Tuple);

    auto *CurFieldStructType = dyn_cast<StructType>(CurFieldType);
    auto CurFieldIsLiteral =
        CurFieldStructType && CurFieldStructType->isLiteral();
    auto CurFieldIsUnion = CurFieldStructType && !CurFieldIsLiteral &&
                           (CurFieldStructType->getName().find("union.") == 0);
    bool CurFieldIsBlockListedStruct = false;

    {
      if (CurFieldStructType &&
          !clFSAN_BLOCKLIST_TAG_FILEPATH.getValue().empty()) {
        auto demangledTypeName =
            demangle(CurFieldStructType->getStructName().str());
        auto Size = M.getDataLayout().getTypeAllocSize(CurFieldStructType);
        std::ifstream BlocklistFile(clFSAN_BLOCKLIST_TAG_FILEPATH.getValue());
        if (BlocklistFile.is_open()) {
          std::string Line;
          while (std::getline(BlocklistFile, Line)) {
            // NOTE: we want to match struct.sockaddr, but not
            // struct.sockaddr_in
            bool containsAsterisk = Line.find('*') != std::string::npos;
            if (containsAsterisk) {
              // if the line contains an asterisk, we check if the demangled
              // type name contains the line without the asterisk
              auto LineWithoutAsterisk = Line;
              LineWithoutAsterisk.erase(std::remove(LineWithoutAsterisk.begin(),
                                                    LineWithoutAsterisk.end(),
                                                    '*'),
                                        LineWithoutAsterisk.end());
              if (demangledTypeName.find(LineWithoutAsterisk) !=
                  std::string::npos) {
                errs() << "[FSAN - TAG] NULL TAG ON STRUCT "
                       << *CurFieldStructType
                       << " (matched blocklist line: " << Line << ")\n";
                CurFieldIsBlockListedStruct = true;
                break;
              }
            } else if (demangledTypeName.find(Line) == 0 && Line.length() > 1) {
              errs() << "[FSAN - TAG] NULL TAG ON STRUCT "
                     << *CurFieldStructType
                     << " (matched blocklist line: " << Line << ")\n";
              CurFieldIsBlockListedStruct = true;
              break;
            }
          }
        }
      }
    }
    if (CurFieldStructType != nullptr && !CurFieldIsLiteral &&
        !CurFieldIsUnion && !CurFieldIsBlockListedStruct) {

      int Count = 0;
      // auto ContainedSubTypes = CurFieldType->getNumContainedTypes();

      auto ContainedSubTyOffsets =
          DL.getStructLayout(CurFieldStructType)->getMemberOffsets();
      auto ContainedSubTypes = CurFieldStructType->getNumElements();
      size_t CurContainedSubTy = 0;
      // for struct types, we go one level deeper
      auto NextL = 0; // NO L

      for (Type *SSty : llvm::reverse(CurFieldType->subtypes())) {
        CurContainedSubTy =
            ContainedSubTyOffsets[ContainedSubTypes - Count - 1] +
            CurFieldOffset;
        AggQueue.push_front(std::make_tuple(
            SSty, 0, NextL, ContainedSubTypes - Count, CurContainedSubTy));
        Count++;
      } // for subtype
    } // if son struct

    else if (CurFieldType->isArrayTy()) {
      const int MaxDepth = 20;
      int ArrayDims = 1; // at least 1 dim
      auto *CurArrayType = dyn_cast<ArrayType>(CurFieldType);
      auto *OuterArrayType = CurArrayType; // for later

      u_int64_t Elements = CurArrayType->getNumElements();
      auto *ElemType = CurArrayType->getArrayElementType();

      while (ElemType->isArrayTy() && ArrayDims <= MaxDepth) {
        CurArrayType = dyn_cast<ArrayType>(ElemType);
        ElemType = CurArrayType->getArrayElementType();
        Elements *= CurArrayType->getNumElements();
        ArrayDims++;
      }
      // check type
      if (ElemType->isStructTy()) {
        // retrieve or create tag vector for struct type
        auto *ElemStructType = dyn_cast<StructType>(ElemType);
        assert(ElemStructType &&
               "Element type of array must be struct for this case.");
        size_t ElemStructSize = DL.getTypeAllocSize(ElemStructType);
        auto *TagVector =
            RetrieveOrCreateTagVector(ElemStructType, M, /*DUMMY*/1);
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
            Tags[ElemOffset + H] = static_cast<uint8_t>(ElemTagValue);
          }
        }
      } // elem is struct
      else {
        uint64_t IdxModuloT_MAX = sonIdx % T_MAX;
        uint64_t IdxDivT_MAX = sonIdx / T_MAX;
        uint64_t T = (IdxModuloT_MAX + IdxDivT_MAX);
        T = T % T_MAX;
        if (T == 0) {
          T = 1;
        }
        uint8_t Tag = T;
        // if it's monodimensional, we tag it with T
        if (ArrayDims == 1) {
          for (uint64_t idx = 0; idx < OuterArrayType->getNumElements();
               idx++) {
            auto el = OuterArrayType->getElementType();
            auto Offset = CurFieldOffset + idx * DL.getTypeAllocSize(el);
            memset(&Tags[Offset], Tag, DL.getTypeAllocSize(el));
          }
        } // if ArrayDims == 1

        else {
          // N-D array case
          ComputeTagsOnNDArray(OuterArrayType, M, DL, ArrayDims, Tags,
                               CurFieldOffset);
        } // array dims > 1
      } // elem is not struct
      auto *arrTy = dyn_cast<ArrayType>(CurFieldType);
      auto ArrayFieldElems = arrTy->getNumElements();

      // NOTE: this does not violate the C std!
      // ONLY ENABLE IF IT'S FULL OF THESE BUGS AND THEY ARE ANNOYING FOR
      // FUZZING
      bool isArray = CurFieldType->isArrayTy();
      // NOTE: FAM can only be at the very end of the struct, but there could
      // be an extra padding member if the size of the FAM is 1.
      bool IsLastField =
          sonIdx == FieldsOffsets.size() ||
          sonIdx == (FieldsOffsets.size() -
                     1); // breaks with padding bytes, they are an extra field

      if (IsLastField && isArray) {

        // NOTE: the field might overlap with compiler-inserted padding
        // TODO:double check that this makes sense in STD
        if (ArrayFieldElems == 0 || ArrayFieldElems == 1) {
          auto RemainderBytes = DL.getTypeAllocSize(Ty) - CurFieldOffset;
          if (clFSAN_FAM) {
            errs() << "[FSAN - TAG] Clearing potential padding at the end of "
                      "struct "
                   << *Ty << " (field: " << *CurFieldType << ", idx " << sonIdx
                   << ", remainder bytes: " << RemainderBytes
                   << ", struct size: " << DL.getTypeAllocSize(Ty) << ")\n";
            memset(&Tags[CurFieldOffset], 0x00, RemainderBytes);
          }
        }
        // FFMPEG fix: remove FPs untagging artifically padded structs? Can
        // be patched in SRC
      } // if LastField
    } else {
      // case : scalar fields, literal structs, unions == ALL SCALAR
      if (CurFieldType->isStructTy() && (CurFieldIsLiteral || CurFieldIsUnion ||
                                         CurFieldIsBlockListedStruct)) {
        // union, literal
        memset(&Tags[CurFieldOffset], 0x00, DL.getTypeAllocSize(CurFieldType));
      } else {
        // scalar field
        uint64_t IdxModuloT_MAX = sonIdx % T_MAX;
        uint64_t IdxDivT_MAX = sonIdx / T_MAX;
        auto T = (IdxModuloT_MAX + IdxDivT_MAX);
        T = T % T_MAX;
        if (T == 0) {
          T = 1;
        }
        uint8_t Tag = T;

        uint8_t CurFieldTag = Tag;
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