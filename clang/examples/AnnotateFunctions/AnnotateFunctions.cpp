#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ParentMapContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Rewrite/Core/Rewriter.h"

#include "llvm/Support/raw_ostream.h"

#include <set>
#include <string>

/** FSan frontend plugin for typing C. */
using namespace clang;

std::set<std::string> AllocatingFunctions = {
    "malloc",         "calloc",        "realloc",       "valloc",
    "posix_memalign", "aligned_alloc", "pvalloc",       "new",
    "new[]",          "operator new",  "operator new[]"};

class AllocationSiteVisitor
    : public RecursiveASTVisitor<AllocationSiteVisitor> {
public:
  explicit AllocationSiteVisitor(Rewriter &R, ASTContext *C)
      : MyRewriter(R), Context(C) {}

  /** Visitor for CallExpr */
  bool VisitCallExpr(CallExpr *Call) {
    if (const auto *Callee = Call->getDirectCallee()) {
      std::string CalleeName = Callee->getQualifiedNameAsString();
      if (CalleeName.empty())
        return true;

      auto lookup = AllocatingFunctions.find(CalleeName);

      if (lookup != AllocatingFunctions.end()) {
        llvm::errs() << "ALLOC: " << CalleeName << " at ";
        Context->getFullLoc(Call->getBeginLoc()).dump();
        llvm::errs() << "\n";
        // get CAST
        // get ARG and look for sizeof
        // get ASSIGNMENT and look for LHS type
        auto Parents = Context->getParents(*Call);
        if (Parents.empty())
          return true;
      }
    }
    return true;
  }
  // operator new is not listed by the above. How so?

  bool VisitCXXNewExpr(CXXNewExpr *New) {
    // llvm::errs() << "NEW: ";
    // Context->getFullLoc(New->getBeginLoc()).dump();
    auto CalleeOperator = New->getOperatorNew();
    if (CalleeOperator) {
      std::string CalleeName = CalleeOperator->getQualifiedNameAsString();
      if (CalleeName.empty())
        return true;

      llvm::errs() << "NEW: " << CalleeName << " at ";
      Context->getFullLoc(New->getBeginLoc()).dump();
      // allocated type?
      // if (New->getAllocatedType() != nullptr) {
      llvm::errs() << "           - Allocated type: "
                   << New->getAllocatedType().getAsString() << "\n";
      // }
      llvm::errs() << "\n";
    }
    return true;
  }

  // bool VisitExpr(Expr *E) {
  //   // visit assignments
  //   if (auto *BinOp = dyn_cast<BinaryOperator>(E)) {
  //     if (BinOp->isAssignmentOp()) {
  //       // only visit assignments of result of function call
  //       auto LHS = BinOp->getLHS()->IgnoreParenCasts();
  //       auto RHS = BinOp->getRHS()->IgnoreParenCasts();
  //       if (auto *Call = dyn_cast<CallExpr>(RHS)) {
  //         if (const auto *Callee = Call->getDirectCallee()) {
  //           std::string CalleeName = Callee->getQualifiedNameAsString();
  //           if (CalleeName.empty())
  //             return true;

  //           llvm::errs() << "ASSIGN: at ";
  //           Context->getFullLoc(BinOp->getBeginLoc()).dump();
  //           llvm::errs() << "\n";
  //         }
  //       }
  //     }
  //   } // if BinaryOperator
  //   else if (auto *Cast = dyn_cast<CStyleCastExpr>(E)) {
  //     auto SubExpr = Cast->getSubExpr()->IgnoreParenCasts();
  //     if (auto *Call = dyn_cast<CallExpr>(SubExpr)) {
  //       if (const auto *Callee = Call->getDirectCallee()) {
  //         std::string CalleeName = Callee->getQualifiedNameAsString();
  //         if (CalleeName.empty())
  //           return true;

  //         llvm::errs() << "CAST: at ";
  //         Context->getFullLoc(Cast->getBeginLoc()).dump();
  //         llvm::errs() << "\n";
  //       }
  //     }
  //   }
  // } // VisitExpr

private:
  Rewriter &MyRewriter;
  ASTContext *Context;
};

class AllocationSiteConsumer : public ASTConsumer {
public:
  AllocationSiteConsumer(CompilerInstance &CI)
      : MyRewriter(CI.getSourceManager(), CI.getLangOpts()),
        Visitor(MyRewriter, &CI.getASTContext()) {}

  virtual void HandleTranslationUnit(clang::ASTContext &Context) override {
    // Traversing the translation unit decl via a RecursiveASTVisitor
    // will visit all nodes in the AST.
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
  }

private:
  Rewriter MyRewriter; // TODO: make sure this is  correctly initialized
  AllocationSiteVisitor Visitor;
};

class AllocationSiteAction : public PluginASTAction {
protected:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 llvm::StringRef) override {
    // this method returns a consumer per TU
    return std::make_unique<AllocationSiteConsumer>(CI);
  }

  bool ParseArgs(const CompilerInstance &CI,
                 const std::vector<std::string> &args) override {
    return true;
  }

  // PluginASTAction::ActionType getActionType() override {
  //   return ReplaceAction;
  // }
};

static FrontendPluginRegistry::Add<AllocationSiteAction>
    X("fsan-frontend", "Typing C and C++ for Fun and Profit");
