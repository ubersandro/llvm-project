#ifndef LLVM_ANALYSIS_TYPECOPILOT_H
#define LLVM_ANALYSIS_TYPECOPILOT_H

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/Compiler.h"
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/BinaryFormat/Dwarf.h>
#include <llvm/IR/Analysis.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/Casting.h>
#include <llvm/Support/TypeName.h>
#include <llvm/Support/raw_ostream.h>

#include <execinfo.h>
#include <iomanip>
#include <iostream>
#include <map>
#include <queue>
#include <regex>
#include <set>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

namespace llvm {

std::map<std::string, std::string> type_trans_map = {
    {"bool", "i1"},           {"short", "i16"},
    {"char", "i8"},           {"int", "i32"},
    {"long", "i64"},          {"long long", "i64"},
    {"unsigned char", "i8"},  {"unsigned short", "i16"},
    {"unsigned long", "i64"}, {"unsigned long long", "i64"},
    {"unsigned int", "i32"},
};

std::string di_to_ir_type(const std::string &di_type) {
  std::string ir_type = di_type;
  // trim the ending multiple *
  int ptr_level = 0;
  while (ir_type.size() > 0 && ir_type.back() == '*') {
    ir_type.pop_back();
    ptr_level++;
  }

  if (ir_type.empty()) {
    return "unk"; // pure AI guess, TODO: look into this
  }

  // general types, in the table
  auto iter = type_trans_map.find(ir_type);
  if (iter != type_trans_map.end()) {
    ir_type = iter->second;
  } else {
    // di_type starts with "struct"
    if (ir_type.find("struct") == 0) {
      ir_type = "\%struct." + ir_type.substr(7);
    } else if (ir_type.find("enum") == 0) {
      ir_type = "i32";
    } else if (ir_type.find("union") == 0) {
      ir_type = "\%union." + ir_type.substr(6);
    } else if (ir_type.find("class") == 0) {
      ir_type = "\%class." + ir_type.substr(6);
    }
  }

  ir_type += std::string(ptr_level, '*');
  return ir_type;
}

// trim suffixing digits from ir types
std::string trim_ir_suffix(std::string &ir_type) {
  std::regex pattern(R"((%struct\.[a-zA-Z_]\w*)\.\d+(\*?))");
  return std::regex_replace(ir_type, pattern, "$1$2");
}

// this class must be iterable to iterate on the types TODO
class TypeSet {
private:
public:
  std::set<std::string> types;
  bool isFunc = false;

  ~TypeSet() { types.clear(); }

  void dump() const {
    // iterate types and print them with a comma
    auto it = types.begin();
    for (; it != types.end(); it++) {
      errs() << *it;
      if (it != types.end())
        errs() << ", ";
    }
  }

  void insert(std::string type) {
    types.insert(type);
    erasePtr();
  }

  void erase(std::string type) { types.erase(type); }

  void insert(TypeSet *other) {
    if (!other)
      return;

    for (auto it = other->types.begin(); it != other->types.end(); it++)
      types.insert(*it);
    erasePtr();
  }

  bool empty() { return types.empty(); }

  int count(std::string type) { return types.count(type); }

  bool hasPtr() { return types.count("ptr"); }

  bool isOpaque() { return types.size() == 1 && hasPtr(); }

  bool isGenericPtr() { return types.size() == 1 && count("void*"); }

  void erasePtr() {
    if (types.size() > 1 && types.count("ptr"))
      types.erase("ptr");
  }

  std::vector<std::string> getTypes() {
    std::vector<std::string> result;
    for (auto it = types.begin(); it != types.end(); it++)
      result.push_back(*it);
    return result;
  }

  bool equals(TypeSet *given) {
    for (auto it = given->begin(); it != given->end(); it++) {
      if (count(*it))
        return true;
    }

    return false;
  }

  bool equalsBase(TypeSet *given) {
    // ground truth
    for (auto it = given->begin(); it != given->end(); it++) {
      for (auto it2 = types.begin(); it2 != types.end(); it2++) {
        std::string type = *it2;
        while (type.back() == '*')
          type.pop_back();
        if (type == *it)
          return true;
      }
    }
    return false;
  }

  int size() { return types.size(); }

  std::string at(int index) { return *next(types.begin(), index); }

  typename std::set<std::string>::iterator begin() { return types.begin(); }
  typename std::set<std::string>::iterator end() { return types.end(); }
}; // class TypeSet

class TypeHelper {
private:
  // drop struct layout
  void dropLayout(std::string &type) {
    if (type.find("\%struct.") == 0 || type.find("\%union.") == 0) {
      type = type.substr(0, type.find(" "));
    }
  }

  // drop array size
  void dropArray(std::string &type) {
    if (type.find("[") == 0) {
      auto pos = type.find(" ") + 3;
      type = type.substr(pos, type.size() - pos - 1);

      if (type.find("[") == 0)
        dropArray(type);

      if (!isOpaque(type))
        type += "*";
    }
  }

public:
  /// get the name of a type
  inline std::string getTypeName(Type *type) {
    std::string str;
    raw_string_ostream rso(str);
    type->print(rso);
    dropArray(str);
    dropLayout(str);

    return str;
  }

  /// check if a type is an opaque pointer
  bool isOpaque(std::string &type) { return type == "ptr"; }
  bool isOpaque(std::set<std::string> &typeset) { return typeset.count("ptr"); }
  bool isOpaque(Type *type) { return getTypeName(type) == "ptr"; }

  // check if a type is ptr to opaque pointer
  bool isPtrToOpaque(std::string &type) {
    return type == "ptr*" || type == "ptr**";
  }
  bool isPtrToOpaque(std::set<std::string> &typeset) {
    return typeset.count("ptr*") || typeset.count("ptr**");
  }

  std::string getReference(Type *type) {
    auto str = getTypeName(type);

    if (isOpaque(str)) {
      return str;
    }
    return str + "*";
  }

  std::string getReference(std::string &type) {
    if (isOpaque(type)) {
      return type;
    }
    return type + "*";
  }

  bool isNotPtrOpaque(std::string &type) {
    return !type.empty() && !isOpaque(type);
  }

  bool isNotPtrOpaque(TypeSet *typeset) {
    if (!typeset)
      return false;
    return !typeset->empty() && !typeset->isOpaque() &&
           !typeset->isGenericPtr();
  }
};

class WorkList {
private:
  std::queue<Instruction *> worklist;
  std::unordered_set<Instruction *> visited;

public:
  WorkList(Module *module) {
    for (auto &func : *module) {
      for (auto &bb : func) {
        for (auto &inst : bb) {
          worklist.push(&inst);
        }
      }
    }
  }

  void push(Instruction *inst) {
    if (visited.count(inst)) {
      return;
    }

    visited.insert(inst);
    worklist.push(inst);
  }

  void push_user(Value *value) {
    if (!value->hasUseList()) {
      return;
    } // handle CMPs with constants
    for (auto user : value->users()) {
      if (auto inst = dyn_cast<Instruction>(user)) {
        worklist.push(inst);
      }
    }
  }

  Instruction *pop() {
    auto inst = worklist.front();
    worklist.pop();
    visited.erase(inst);
    return inst;
  }

  bool empty() { return worklist.empty(); }
}; // class WorkList

class TypeGraph {
  using TypeMap = std::map<Value *, TypeSet *>;

private:
  const bool DEBUG = false;
  bool isNotPtrOpaque(std::string type) {
    return !type.empty() && type != "ptr";
  }
  bool isNotPtrOpaque(std::set<std::string> typeset) {
    return !typeset.empty() && !typeset.count("ptr");
  }

  // bool isInternal(Value *v) {
  //   auto name = v->getName();
  //   if (name.starts_with("."))
  //     return true;
  //   if (name.count(".") > 1)
  //     return true;
  //   if (name.count(".") == 1) {
  //     auto subname = name.split(".").second;
  //     for (auto ch : subname) {
  //       if (!isDigit(ch))
  //         return true;
  //     }
  //   }

  //   return false;
  // }

public:
  TypeMap globalMap;
  std::map<Function *, TypeMap *> localMap;

  ~TypeGraph() {
    for (auto &pair : globalMap) {
      delete pair.second;
    }
    for (auto &pair : localMap) {
      for (auto &pair2 : *pair.second) {
        delete pair2.second;
      }
      delete pair.second;
    }
  }

  /// get the type of a value
  TypeSet *get(Function *scope, Value *key) {
    // first check local type
    if (scope && localMap.find(scope) != localMap.end()) {
      TypeMap *localTypeMap = localMap[scope];
      auto it = localTypeMap->find(key);
      if (it != localTypeMap->end())
        return it->second;
    }

    // check global type
    auto it = globalMap.find(key);
    if (it != globalMap.end())
      return it->second;

    return nullptr;
  }

  /// merge multiple types into one value's type
  // return true if the type is updated, false if not changed
  bool put(Function *scope, Value *key, TypeSet *value, bool isFunc = false) {
    // no value, quick return
    if (!value)
      return false;

    TypeSet *to_add = new TypeSet();
    to_add->insert(value);

    // find existing type
    auto old = get(scope, key);

    if (old) {
      // filter out ptr* type
      // FIXME delete stale debug stuff
      if (DEBUG && to_add->count("ptr**")) {
        key->dump();
        errs() << "current type: ";
        old->dump();
        errs() << "\n";

        errs() << "stack trace:\n";
        char **strings;
        size_t i, size;
        enum Constexpr { MAX_SIZE = 1024 };
        void *array[MAX_SIZE];
        size = backtrace(array, MAX_SIZE);
        strings = backtrace_symbols(array, size);
        for (i = 0; i < size; i++)
          errs() << strings[i] << "\n";
        free(strings);
      }

      // filter out subtype problems
      for (auto &type : to_add->getTypes()) {
        // if old contains type.reference(), then skip
        if (old->count(type + "*")) {
          to_add->erase(type);
        } else if (type.back() == '*' &&
                   old->count(type.substr(0, type.size() - 1))) {
          // if old contains type.dereference(), then skip
          to_add->erase(type);
        }
      }
    }

    if (old == nullptr)
      old = new TypeSet();

    if (to_add->empty()) {
      delete to_add;
      return false;
    }

    // check if old == value
    if (old->equals(to_add)) {
      delete to_add;
      return false;
    }

    // update type
    old->insert(to_add);
    delete to_add;

    if (isFunc)
      old->isFunc = true;

    if (scope) { // test scope
      auto it = localMap.find(scope);
      if (it != localMap.end()) // update local map
        (*it->second)[key] = old;
      else {
        localMap[scope] = new TypeMap();
        (*localMap[scope])[key] = old;
      }
    } else { // no scope, update global map
      globalMap[key] = old;
    }

    return true;
  }

  /// merge a single type into one value's type
  bool put(Function *scope, Value *key, std::string value,
           bool isFunc = false) {
    // find existing type
    auto old = get(scope, key);

    if (old) {
      // filter out ptr* type
      if (DEBUG && value == "ptr**") {
        key->dump();
        errs() << "current type: ";
        old->dump();
        errs() << "\n";

        errs() << "stack trace:\n";
        char **strings;
        size_t i, size;
        enum Constexpr { MAX_SIZE = 1024 };
        void *array[MAX_SIZE];
        size = backtrace(array, MAX_SIZE);
        strings = backtrace_symbols(array, size);
        for (i = 0; i < size; i++)
          errs() << strings[i] << "\n";
        free(strings);
      }

      // filter out subtype problems
      if (old->count(value + "*")) {
        return false;
      } else if (value.back() == '*' &&
                 old->count(value.substr(0, value.size() - 1))) {
        return false;
      }
    }

    if (old == nullptr)
      old = new TypeSet();

    // check if old == value
    if (old->count(value))
      return false;

    // update type
    old->insert(value);

    if (isFunc)
      old->isFunc = true;

    // should not be a global value
    if (!dyn_cast<GlobalValue>(key) && scope) {
      auto it = localMap.find(scope);
      if (it != localMap.end()) // update local map
        (*it->second)[key] = old;
      else {
        localMap[scope] = new TypeMap();
        (*localMap[scope])[key] = old;
      }
    } else { // no scope, update global map
      globalMap[key] = old;
    }

    return true;
  }

  /// check if a value is an opaque pointer
  bool isOpaque(Function *scope, Value *key) {
    auto typeSet = get(scope, key);
    return typeSet && typeSet->count("ptr");
  }

  /// get the pointer type of a value
  TypeSet *reference(Function *scope, Value *key) {
    auto ret = new TypeSet();
    auto old = get(scope, key);

    if (!old)
      return ret;

    for (auto &type : old->getTypes()) {
      // if type ends with "**", skip ***p
      if (type.size() > 2 && type.substr(type.size() - 2) == "**") {
        continue;
      }

      if (type != "ptr")
        ret->insert(type + "*");
    }

    return ret;
  }

  /// get the dereferenced type of a value
  TypeSet *dereference(Function *scope, Value *key) {
    auto ret = new TypeSet();
    auto old = get(scope, key);

    if (!old)
      return ret;

    for (auto &type : old->getTypes()) {
      if (type.back() == '*') {
        ret->insert(type.substr(0, type.size() - 1));
      }
    }

    return ret;
  }

  std::vector<TypeMap *> getAllMap() {
    std::vector<TypeMap *> ret;
    ret.push_back(&globalMap);
    for (auto &pair : localMap) {
      ret.push_back(pair.second);
    }
    return ret;
  }

  int varSize() {
    int ret = globalMap.size();
    for (auto &pair : localMap) {
      ret += pair.second->size();
    }
    return ret;
  }
}; // class TypeGraph

class LLVMHelper {
public:
  TypeHelper tyHelper;
  virtual void initialize(Module *module, TypeGraph *tg) = 0;
  virtual ~LLVMHelper() {}
};

cl::opt<std::string> TypeSrc("type-src", cl::desc("Type source"),
                             cl::value_desc("type source"), cl::init("di"));

class DebugInfoHelper : public LLVMHelper {
private:
  const bool RESOLVE_TYPEDEF = true;

  // maps struct type to DIType (derived, composite)
  std::map<StructType *, DIType *> structMap;
  std::map<Value *, std::vector<DILocalVariable *>> diLocalMap;

public:
  bool hasDebugInfo(Module &M) {
    for (auto &F : M)
      for (auto &BB : F)
        for (auto &I : BB)
          if (auto DILoc = I.getDebugLoc())
            return true;
    return false;
  }

  void initialize(Module *module, TypeGraph *tg) override {
    // map structure type to DIType
    DebugInfoFinder finder;
    finder.processModule(*module);

    for (auto s : module->getIdentifiedStructTypes()) {
      // NOTE: literal structs are skipped. TODO: make sure they no longer
      // exist.
      if (!s->hasName())
        continue;
      auto isClass = s->getName().find("class.") != StringRef::npos;
      auto structName = s->getName();

      if (!isClass) {
        structName.consume_front("struct.");

      } // is not class
      else {
        // TODO: investigate this, it does not produce anything useful now
        // errs() << "[TypeCopilot] Found class: " << structName << "\n";
        structName.consume_front("class.");
      } // CLASS CASE

      for (auto type : finder.types()) {
        // typedef
        if (auto *derived = dyn_cast<DIDerivedType>(type)) {
          if (derived->getTag() == dwarf::DW_TAG_typedef) {
            if (derived->getName() == structName) {
              structMap.insert({s, derived->getBaseType()});
              break;
            }
          } // is TypeDef
        }
        // struct
        else if (auto *composite = dyn_cast<DICompositeType>(type)) {
          if (composite->getTag() == dwarf::DW_TAG_structure_type) {
            if (composite->getName() == structName) {
              // empty elements, skip
              if (composite->getElements().empty())
                continue;

              structMap.insert({s, composite});
              break;
            } // is struct
          } // is struct
        } // is composite
      } // for types
    } // for struct types

    for (auto &global : module->globals()) {
      SmallVector<DIGlobalVariableExpression *> di_global_exps;
      global.getDebugInfo(di_global_exps);

      if (di_global_exps.empty()) {
        continue;
      }

      for (auto di_global_exp : di_global_exps) {
        auto di_global = di_global_exp->getVariable();
        auto di_type_name = getDITypeName(di_global->getType()) + "*";
        tg->put(nullptr, &global, di_to_ir_type(di_type_name));
      }
    }

    // parse di local variables
    for (auto &F : *module) {
      for (auto &BB : F) {
        for (auto &I : BB) {
          parseDILocalVar(I, diLocalMap);
        }
      }
    }
    // errs() << "[TypeCopilot] Instruction initialization...\n";
    for (auto &func : *module) {
      for (auto &basic_block : func) {
        for (auto &inst : basic_block) {

          // get value
          Value *value = dyn_cast<Value>(&inst);
          if (auto store = dyn_cast<StoreInst>(&inst)) {
            value = store->getValueOperand();
          } // is store inst

          if (diLocalMap.find(value) != diLocalMap.end()) {
            for (auto di_local : diLocalMap[value]) {
              auto di_type_name = getDITypeName(di_local->getType());

              if (dyn_cast<AllocaInst>(value)) {
                di_type_name += "*";
              }
              tg->put(&func, value, di_to_ir_type(di_type_name));
            }
          }
        }
      }
    }
    
    for (auto &func : *module) {
      Value *funcValue = dyn_cast<Value>(&func);

      // get DISubprogram
      auto *subprogram = func.getSubprogram();

      if (!subprogram) {
        auto type = func.getFunctionType();
        auto retType = type->getReturnType();
        tg->put(nullptr, funcValue, tyHelper.getTypeName(retType), true);
      } else {
        auto *subroutinetype = subprogram->getType();
        auto typearray = subroutinetype->getTypeArray();
        if (typearray.size() == 0)
          continue;
        // TODO: how can some functions not have a type array?
        // process return type
        auto di_type_name = getDITypeName(typearray[0]);
        // errs() << "[TypeCopilot] Function: " << func.getName() << ", return
        // type: "
        //        << di_type_name << ", di_to_ir_type: " <<
        //        di_to_ir_type(di_type_name) << "\n";
        tg->put(nullptr, funcValue, di_to_ir_type(di_type_name), true);
        // errs()<< "HERE" << "\n";
        // process parameters
        for (size_t i = 1; i < typearray.size(); ++i) {
          auto type = typearray[i];
          // errs()<< "HERE HERE" << "\n";

          if (!type) // type can be null in variable func parameters
            continue;

          if (i - 1 < func.arg_size()) { // avoid overflow
            // type from DI subprogram
            auto param = func.getArg((int)(i - 1));
            auto di_type_name = getDITypeName(type);
            tg->put(&func, param, di_to_ir_type(di_type_name));

            // type from DI local var
            if (diLocalMap.find(param) != diLocalMap.end()) {
              for (auto di_local : diLocalMap[param]) {
                auto di_type_name = getDITypeName(di_local->getType());
                tg->put(&func, param, di_to_ir_type(di_type_name));
              }
            }
          }
        }
      }
    } // for function

  } // initialize

  void parseDILocalVar(
      Instruction &inst,
      std::map<Value *, std::vector<DILocalVariable *>> &diLocalMap) {
    // check if is call inst
    if (auto *call = dyn_cast<CallInst>(&inst)) {
      auto call_func = call->getCalledFunction();
      if (!call_func)
        return;
      if (call_func->arg_size() < 2)
        return;

      // check invoked function is intrinsic llvm debug function
      if (call_func && call_func->isIntrinsic() &&
          call_func->getName().starts_with("llvm.dbg")) {

        auto val = call->getArgOperand(0);
        MetadataAsValue *mtv0 = dyn_cast_or_null<MetadataAsValue>(val);
        Metadata *mt0 = mtv0->getMetadata();
        ValueAsMetadata *vmt = dyn_cast_or_null<ValueAsMetadata>(mt0);
        if (!vmt)
          return;
        Value *real_val = vmt->getValue();

        // get the second argument, which stores `DILocalVariable`
        if (auto arg = call->getArgOperand(1)) {
          auto metadata = dyn_cast<MetadataAsValue>(arg)->getMetadata();
          DILocalVariable *di_value = dyn_cast<DILocalVariable>(metadata);
          // one value can map to multiple values, so save in vectors
          if (diLocalMap.find(real_val) != diLocalMap.end()) {
            diLocalMap[real_val].push_back(di_value);
          } else {
            diLocalMap[real_val] = {di_value};
          }
        }
      }
    }
  } // parseDILocalVar

  std::string getDIStructField(StructType *structType, uint64_t index) {
    // iterate over all DICompositeType
    auto pos = structMap.find(structType);
    if (pos == structMap.end()) {
      return "";
    }

    auto diStructType = static_cast<DICompositeType *>(pos->second);
    auto elements = diStructType->getElements();
    if (index >= elements.size()) {
      return "";
    }

    auto element = elements[index];
    if (auto *derivedType = dyn_cast<DIDerivedType>(element)) {
      auto baseTypeName = getDITypeName(derivedType->getBaseType());
      return di_to_ir_type(baseTypeName);
    }
    return "";
  }

  std::string getDITypeName(DIType *ditype) {
    if (!ditype)
      return "void";

    std::string name = "";

    // dump DIType according to DITag
    auto tag = ditype->getTag();
    switch (tag) {

    case dwarf::DW_TAG_base_type:
      name = (ditype->getName() == "_Bool") ? "bool" : ditype->getName().str();
      break;
    case dwarf::DW_TAG_enumeration_type:
      name = "enum " + ditype->getName().str();
      break;
    case dwarf::DW_TAG_array_type: {
      auto *composite = dyn_cast<DICompositeType>(ditype);
      auto basename = composite->getBaseType() != nullptr
                          ? getDITypeName(composite->getBaseType())
                          : "void";
      // infer subrange
      int subrangeCount = 0;
      auto elements = composite->getElements(); // get elements
      for (auto element : elements) {
        if (dyn_cast<DISubrange>(element))
          subrangeCount++;
      }
      name =
          basename + std::string(subrangeCount, '*'); // multi-dimensional array
    } break;
    case dwarf::DW_TAG_pointer_type: {
      auto *derived = dyn_cast<DIDerivedType>(ditype);
      auto basename = derived->getBaseType() != nullptr
                          ? getDITypeName(derived->getBaseType())
                          : "void";
      // if (basename == "void")
      //     name = "ptr";
      // else
      name = basename + "*";
    } break;
    case dwarf::DW_TAG_structure_type:
      name = "struct " + ditype->getName().str();
      break;
    case dwarf::DW_TAG_typedef:
      if (RESOLVE_TYPEDEF) {
        auto *derived = dyn_cast<DIDerivedType>(ditype);
        auto basetype = derived->getBaseType();
        if (basetype) {
          name = getDITypeName(basetype);
          if (name == "") {
            name = ditype->getName().str();
          }
        } else {
          name = ditype->getName().str();
        }
      } else {
        name = ditype->getName().str();
      }
      break;
    case dwarf::DW_TAG_volatile_type:
    case dwarf::DW_TAG_restrict_type:
    case dwarf::DW_TAG_const_type: {
      auto *derived = dyn_cast<DIDerivedType>(ditype);
      auto basename = derived->getBaseType() != nullptr
                          ? getDITypeName(derived->getBaseType())
                          : "void";
      name = basename;
    } break;
    case dwarf::DW_TAG_union_type: {
      name = "union " + ditype->getName().str();
    } break;
    case dwarf::DW_TAG_subroutine_type: {
      auto *subroutine = dyn_cast<DISubroutineType>(ditype);
      name = subroutine->getName();
    } break;
    case dwarf::DW_TAG_class_type: {
      
      std::string ns = "";
      auto scope = ditype->getScope();
      if (scope) {
        auto *discope = dyn_cast<DIScope>(scope);
        if (discope) {
          auto porcodio = discope->getName();
          // if (porcodio != nullptr) {
          std::string ns_name = porcodio.str();
          if (!ns_name.empty())
            ns = ns_name + "::";
        }
      }

      name = "class " + ns + ditype->getName().str();
      // name = ns + ditype->getName().str();
      errs() << "[TypeCopilot] Found class " << name << " with SCOPE ns: " << ns
             << "\n";
    } break;
    case dwarf::DW_TAG_reference_type: {
      // TODO: this is AI bullshit, look into it
      auto *derived = dyn_cast<DIDerivedType>(ditype);
      auto basename = derived->getBaseType() != nullptr
                          ? getDITypeName(derived->getBaseType())
                          : "void";
      name = basename + "&";
    } break;

    case dwarf::DW_TAG_ptr_to_member_type: {
      // TODO
      errs() << "[TypeCopilot] ptr to member DIType: ";
      ditype->print(errs());
      errs() << ", ";

      auto *derived = dyn_cast<DIDerivedType>(ditype);
      if (!derived) {
        errs() << "[TypeCopilot] Failed to cast to DIDerivedType\n";
        return "";
      }

      derived->getBaseType()->print(errs());
      errs() << "\n";
      auto *subroutine = dyn_cast<DISubroutineType>(derived->getBaseType());
      if (subroutine) {
        auto typearray = subroutine->getTypeArray();
        if (typearray.size() > 0) {
          auto ret_type = getDITypeName(typearray[0]);
          errs() << "[TypeCopilot] ptr to member function return type: "
                 << ret_type << "\n";
        }
      }
      // TODO: how should I use this?
    } break;

    default:
      errs() << "[TypeCopilot] HANDLE DWARF TAG -> " << tag << "\n";
      break;
    }
    // errs() << "[TypeCopilot] getDITypeName RET " << name << ", tag: " << tag
    // << "\n";
    return name;
  }
}; // class DebugInfoHelper

class TypeAlias {
private:
  Module *m;
  TypeGraph *tg;
  WorkList *worklist;
  TypeHelper *tyHelper;
  DebugInfoHelper *diHelper;

public:
  TypeAlias(Module *m, TypeGraph *tg, WorkList *worklist,
            DebugInfoHelper *diHelper) {
    this->m = m;
    this->tg = tg;
    this->worklist = worklist;
    this->diHelper = diHelper;
  }

  void processPhi(Function *scope, PHINode &phi) {
    bool r_updated = false;
    Value *r = dyn_cast<Value>(&phi);

    for (unsigned int i = 0; i < phi.getNumIncomingValues(); ++i) {
      Value *v = phi.getIncomingValue(i);
      if (!tg->isOpaque(scope, v) && tg->isOpaque(scope, r)) {
        if (tg->put(scope, r, tg->get(scope, v)))
          r_updated = true;
      }
    }

    if (r_updated)
      worklist->push_user(r);
  }

  void processExtractValue(Function *scope, ExtractValueInst &extract) {
    // associate R with the type of the value that gets extracted
    Value *r = dyn_cast<Value>(&extract);
    Value *agg = extract.getAggregateOperand();
    auto idx = extract.getIndices()[0];
    // Type* aggType = agg->getType();
    Type *resType = extract.getType();

    errs() << "[TypeCopilot] processExtractValue: " << extract << ", " << *agg
           << ", " << idx << ", extracted el type: " << *resType << "\n";

    // if (!tg->isOpaque(scope, agg) && tg->isOpaque(scope, r)) {
    // if (tg->isOpaque(scope, r)) {
    //   if (tg->put(scope, r, res))
    //     worklist->push_user(r);
    // }
  }

  void processInsertValue(Function *scope, InsertValueInst &insert) {
    Value *r = dyn_cast<Value>(&insert);
    Value *agg = insert.getAggregateOperand();
    Value *val = insert.getInsertedValueOperand();
    errs() << "[TypeCopilot] processInsertValue: " << insert << ", " << *agg
           << ", " << *val << "\n";

    if (!tg->isOpaque(scope, agg) && tg->isOpaque(scope, r)) {
      if (tg->put(scope, r, tg->get(scope, agg)))
        worklist->push_user(r);
    }

    if (!tg->isOpaque(scope, val) && tg->isOpaque(scope, r)) {
      if (tg->put(scope, r, tg->get(scope, val)))
        worklist->push_user(r);
    }
  }

  void processSelect(Function *scope, SelectInst &select) {
    bool r_updated = false;
    Value *r = dyn_cast<Value>(&select);
    Value *a = select.getTrueValue();
    Value *b = select.getFalseValue();

    auto typeB = tg->get(scope, b);
    if (tyHelper->isNotPtrOpaque(typeB)) {
      if (tg->put(scope, a, tg->get(scope, b)))
        worklist->push_user(a);

      if (tg->put(scope, r, tg->get(scope, b)))
        r_updated = true;
    }

    auto typeA = tg->get(scope, a);
    if (tyHelper->isNotPtrOpaque(typeA)) {
      if (tg->put(scope, b, tg->get(scope, a)))
        worklist->push_user(b);

      if (tg->put(scope, r, tg->get(scope, a)))
        r_updated = true;
    }

    if (r_updated)
      worklist->push_user(r);
  }

  void processFieldOf(Function *scope, GetElementPtrInst &gep) {
    // TODO: this cannot work
    // errs() << "[TypeCopilot] processFieldOf: " << gep
    //        << ", noperands: " << gep.getNumOperands() << "\n";
    Value *base = gep.getPointerOperand();
    Type *baseType = gep.getSourceElementType();

    // base type
    auto baseName = tyHelper->getTypeName(baseType);
    if (tg->isOpaque(scope, base) && tyHelper->isNotPtrOpaque(baseName)) {
      if (tg->put(scope, base, tyHelper->getReference(baseName)))
        worklist->push_user(base);
    }

    // infer left hand side value's type
    std::string typeName;
    Value *lhs = dyn_cast<Value>(&gep);

    // start from 2, skip the first index
    for (unsigned int i = 2; i < gep.getNumOperands(); ++i) {
      Value *index = gep.getOperand(i);
      if (auto *constIndex = dyn_cast<ConstantInt>(index)) {
        // if the index is a constant, adjust the type
        uint64_t index = constIndex->getZExtValue();

        if (auto *structType = dyn_cast<StructType>(baseType)) {
          if (index < structType->getNumElements()) {
            baseType = structType->getElementType(index);
            typeName = tyHelper->getTypeName(baseType);

            // if baseType is op, divert to DIType
            if (tyHelper->isOpaque(typeName) && i == gep.getNumOperands() - 1) {
              typeName = diHelper->getDIStructField(structType, index);
            }
          }
        } else if (auto *arrayType = dyn_cast<ArrayType>(baseType)) {
          baseType = arrayType->getElementType();
        } else if (auto *vectorType = dyn_cast<VectorType>(baseType)) {
          baseType = vectorType->getElementType();
        } else {
          // should not reach here
          errs() << "[ERR] unknown type: ";
          baseType->dump();
        }
      } else {
        if (auto *arrayType = dyn_cast<ArrayType>(baseType)) {
          baseType = arrayType->getElementType();
        } else if (auto *vectorType = dyn_cast<VectorType>(baseType)) {
          baseType = vectorType->getElementType();
        } else {
          // should not reach here
          errs() << "[ERR] unknown index: ";
          index->dump();
          assert(false && "GEP index is not constant");
          // exit(1);
        }
      }
    }

    if (tyHelper->isNotPtrOpaque(
            typeName)) { // tg->isOpaque(scope, lhs) &&  REMOVED vaffanculo
      if (tg->put(scope, lhs, tyHelper->getReference(typeName))) {
        // errs() << "[DBG] GEP update LHS" << *lhs << " to " << typeName
        //        << " isOpaque? " << tg->isOpaque(scope, lhs) << "
        //        isNotPtrOpaque? "
        //        << tyHelper->isNotPtrOpaque(typeName) << "\n";
        worklist->push_user(lhs);

      } // NOTE: there could be no update due to how the put is implemented,
        // there's more to it

      // TODO: debug the following, it's not over yet
      // else
      //   errs() << "[DBG] GEP NO update LHS" << *lhs << " to " << typeName
      //          << " isOpaque? " << tg->isOpaque(scope, lhs) << "
      //          isNotPtrOpaque? "
      //          << tyHelper->isNotPtrOpaque(typeName) << "\n";
    }
  }

  void processCast(Function *scope, CastInst &cast) {
    // Value* src = cast.getOperand(0);
    Value *dst = dyn_cast<Value>(&cast);
    auto dstType = tyHelper->getTypeName(cast.getDestTy());

    if (tg->put(scope, dst, dstType))
      worklist->push_user(dst);
  }

  void processCopy(Function *scope, CallInst &call) {
    Value *dst = call.getArgOperand(0);
    Value *src = call.getArgOperand(1);

    auto dstType = tg->get(scope, dst);
    if (tyHelper->isNotPtrOpaque(dstType)) {
      if (tg->put(scope, src, dstType))
        worklist->push_user(src);
    }

    auto srcType = tg->get(scope, src);
    if (tyHelper->isNotPtrOpaque(srcType)) {
      if (tg->put(scope, dst, srcType))
        worklist->push_user(dst);
    }
  }

  void processCall(Function *scope, CallInst &call) {
    Function *calledFunc = call.getCalledFunction();

    // is direct call
    if (calledFunc) {
      if (calledFunc->hasName()) {
        auto funcName = calledFunc->getName();
        if (funcName.starts_with("llvm.memcpy") ||
            funcName.starts_with("llvm.memmove"))
          processCopy(scope, call);
        else if (funcName.starts_with("llvm.")) // llvm instrinsic
          return;
      }

      // Get the number of parameters in the called function
      FunctionType *FTy = calledFunc->getFunctionType();
      unsigned numParams = FTy->getNumParams();

      // handle parameters
      for (unsigned i = 0; i < numParams; ++i) {
        Value *argValue = call.getArgOperand(i);
        Value *paramValue = calledFunc->getArg(i);

        // argValue flows to paramValue
        auto argType = tg->get(scope, argValue);
        if (tyHelper->isNotPtrOpaque(argType))
          if (tg->put(calledFunc, paramValue, argType))
            worklist->push_user(paramValue);
      }
    } else {
      // TODO: indirect call
      // Value *calledValue = call.getCalledOperand();
      // errs() << "[DBG] Indirect call found: ";
      // auto xx = calledValue->stripPointerCasts();
      // errs() << *xx << "\n";
      // Function *f =
      // dyn_cast<Function>(calledValue->stripPointerCasts()); if (f) {
      //     errs() << "[DBG] Indirect call to " << f->getName() << "\n";
      // }
    }

    // process return value
    Value *dst = dyn_cast<Value>(&call);
    auto dstType = tg->get(nullptr, calledFunc);
    if (tyHelper->isNotPtrOpaque(dstType))
      if (tg->put(scope, dst, dstType))
        worklist->push_user(dst);
  }

  void processLoad(Function *scope, LoadInst &load) {
    Value *src = load.getPointerOperand();
    Value *dst = dyn_cast<Value>(&load);

    auto deref = tg->dereference(scope, src);
    if (tyHelper->isNotPtrOpaque(deref))
      if (tg->put(scope, dst, deref))
        worklist->push_user(dst);
    delete deref;

    auto ref = tg->reference(scope, dst);
    if (tyHelper->isNotPtrOpaque(ref))
      if (tg->put(scope, src, ref))
        worklist->push_user(src);
    delete ref;
  }

  void processStore(Function *scope, StoreInst &store) {
    Value *src = store.getValueOperand();
    Value *dst = store.getPointerOperand();

    auto ref = tg->reference(scope, src);
    if (tyHelper->isNotPtrOpaque(ref))
      if (tg->put(scope, dst, ref))
        worklist->push_user(dst);
    delete ref;

    auto deref = tg->dereference(scope, dst);
    if (tyHelper->isNotPtrOpaque(deref))
      if (tg->put(scope, src, deref))
        worklist->push_user(src);
    delete deref;
  }

  void processBinary(Function *scope, BinaryOperator &binop) {
    bool r_updated = false;
    Value *a = binop.getOperand(0);
    Value *b = binop.getOperand(1);
    Value *r = dyn_cast<Value>(&binop);

    auto typeB = tg->get(scope, b);
    if (tyHelper->isNotPtrOpaque(typeB)) {
      if (tg->put(scope, a, tg->get(scope, b)))
        worklist->push_user(a);
      if (tg->put(scope, r, tg->get(scope, b)))
        r_updated = true;
    }

    auto typeA = tg->get(scope, a);
    if (tyHelper->isNotPtrOpaque(typeA)) {
      if (tg->put(scope, b, tg->get(scope, a)))
        worklist->push_user(b);
      if (tg->put(scope, r, tg->get(scope, a)))
        r_updated = true;
    }

    if (r_updated)
      worklist->push_user(r);
  }

  void processCmp(Function *scope, CmpInst &cmp) {
    // TODO: can this be improved?
    // get value a and b
    Value *a = cmp.getOperand(0);
    Value *b = cmp.getOperand(1);

    // type mismatch between a and b
    if (tg->isOpaque(scope, a) && !tg->isOpaque(scope, b)) {
      if (tg->put(scope, a, tg->get(scope, b)))
        worklist->push_user(a);
    } else if (tg->isOpaque(scope, b) && !tg->isOpaque(scope, a)) {
      if (tg->put(scope, b, tg->get(scope, a)))
        worklist->push_user(b);
    }
  }
}; // class TypeAlias

class TypeCopilotResult {
private:
  TypeGraph *tg;

public:
  DebugInfoHelper *helper;
  TypeCopilotResult(TypeGraph *tg = nullptr, DebugInfoHelper *helper = nullptr)
      : tg(tg), helper(helper) {} // TypeCopilotResult
  const TypeSet *lookup(Value *v, Function *f) const {
    return tg->get(f, v);
  } // lookup
};

// from LLVM Docs: If you require interprocedural analysis, it should be a Pass.

class TypeReconstructionAnalysis
    : public AnalysisInfoMixin<TypeReconstructionAnalysis> {
  friend AnalysisInfoMixin<TypeReconstructionAnalysis>;

private:
  TypeGraph *tg;
  TypeAlias *alias;
  WorkList *worklist;
  DebugInfoHelper *diHelper;
  TypeHelper *tyHelper;
  std::unique_ptr<TypeCopilotResult> Ret;
  Module *module;

public:
  using Result = TypeCopilotResult;
  static llvm::AnalysisKey Key;

  explicit TypeReconstructionAnalysis() {}

  TypeCopilotResult run(Module &M, ModuleAnalysisManager &MAM) {
    // TODO: debug cases in which the name of some vars of functions is "". This
    // can break and put rogue data inside the graph. There are many occurrences
    // of just "*" without any further information.
    DebugInfoHelper *diHelper = new DebugInfoHelper();
    tg = new TypeGraph();
    diHelper->initialize(&M, tg);
    worklist = new WorkList(&M);
    alias = new TypeAlias(&M, tg, worklist, diHelper);
    std::set<const char *> UnhandledOpcodes;
    if (!diHelper->hasDebugInfo(M)) {
      errs() << "[TypeCopilot] WARNING: " << M.getName()
             << " has no debug info! Type reconstruction will not happen.\n";
      return nullptr;
    }

    while (!worklist->empty()) {
      auto inst = worklist->pop();
      if (auto *cast = dyn_cast<CastInst>(inst)) {
        alias->processCast(cast->getFunction(), *cast);
      } else if (auto *load = dyn_cast<LoadInst>(inst)) {
        alias->processLoad(load->getFunction(), *load);
      } else if (auto *store = dyn_cast<StoreInst>(inst)) {
        alias->processStore(store->getFunction(), *store);
      } else if (auto *binop = dyn_cast<BinaryOperator>(inst)) {
        alias->processBinary(binop->getFunction(), *binop);
      } else if (auto *phi = dyn_cast<PHINode>(inst)) {
        alias->processPhi(phi->getFunction(), *phi);
      } else if (auto *gep = dyn_cast<GetElementPtrInst>(inst)) {
        alias->processFieldOf(gep->getFunction(), *gep);
      } else if (auto *cmp = dyn_cast<CmpInst>(inst)) {
        alias->processCmp(cmp->getFunction(), *cmp);
      } else if (auto *call = dyn_cast<CallInst>(inst)) {
        alias->processCall(call->getFunction(), *call);
      } else if (auto *select = dyn_cast<SelectInst>(inst)) {
        alias->processSelect(select->getFunction(), *select);
      }
      // else if(auto* extractvalue = dyn_cast<ExtractValueInst>(inst)) {
      //   alias->processExtractValue(extractvalue->getFunction(),
      //   *extractvalue);
      // } else if(auto* insertvalue = dyn_cast<InsertValueInst>(inst)) {
      //   alias->processInsertValue(insertvalue->getFunction(), *insertvalue);
      // }
      else {
        UnhandledOpcodes.insert(inst->getOpcodeName());
      }
      // allocas, ret, invoke, call, br, extractvalue etc.
      // NOTE: allocas are handled elsewhere, it's fine
      // TODO: potentially handle extractvalue and insertvalue
    } // while

    for (auto *t : UnhandledOpcodes) {
      errs() << "[DBG] Unhandled Inst Opcode: ";
      errs() << t;
      errs() << "\n";
    }
    Ret = std::make_unique<TypeCopilotResult>(tg, diHelper);
    return *Ret;
  }
  const TypeCopilotResult &getResult() const { return *Ret; }
}; // class TypeReconstructionAnalysis
} // namespace llvm

#endif // LLVM_ANALYSIS_TYPECOPILOT_H

// Provide definition for the static AnalysisKey
namespace llvm {
inline AnalysisKey TypeReconstructionAnalysis::Key;
}