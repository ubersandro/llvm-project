#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Refactoring/AtomicChange.h"
#include "clang/Tooling/Tooling.h"

#include "clang/Tooling/Transformer/MatchConsumer.h"
#include "clang/Tooling/Transformer/Parsing.h"
#include "clang/Tooling/Transformer/RangeSelector.h"
#include "clang/Tooling/Transformer/RewriteRule.h"
#include "clang/Tooling/Transformer/SourceCode.h"
#include "clang/Tooling/Transformer/SourceCodeBuilders.h"
#include "clang/Tooling/Transformer/Stencil.h"
#include "clang/Tooling/Transformer/Transformer.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include <clang/Rewrite/Core/Rewriter.h>
#include <iostream>
#include <set>
#include <string>

/**
 * FSan frontend plugin for typing C.
 * This plugin is intended to be used with the FSan runtime to type C code.
 * - Typing strategy for C-like allocators: malloc(...) becomes
 * typed_malloc(..., "type"), where "type" is the type of the pointer being
 * allocated.
 * - Typing strategy for C++-like allocators: new T(...) becomes
 * typed_new<T>(..., "type"), where "type" is the type of the pointer being
 * allocated with all the generics info in place.
 *
 */

using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::transformer;
using namespace clang::tooling;

class DebugAllocCallback : public MatchFinder::MatchCallback {
public:
  void run(const MatchFinder::MatchResult &Result) override {
    const auto *Call = Result.Nodes.getNodeAs<CallExpr>("call");
    // const auto *DRE = Result.Nodes.getNodeAs<DeclRefExpr>("allocCall");
    const auto *DRE = Call->getDirectCallee()
                          ? Result.Nodes.getNodeAs<DeclRefExpr>("allocCall")
                          : nullptr;
    llvm::errs() << "=== MATCH FIRED ===\n";
    if (Call) {
      llvm::errs() << "CallExpr found: ";
      Call->dump();
    } else {
      llvm::errs() << "CallExpr NOT found\n";
    }
    if (DRE) {
      llvm::errs() << "DeclRefExpr found: " << DRE->getDecl()->getNameAsString()
                   << "\n";
    } else {
      llvm::errs() << "DeclRefExpr NOT found\n";
    }
  }
};

std::set<std::string> AllocatingFunctions = {
    "malloc",         "calloc",        "realloc",       "valloc",
    "posix_memalign", "aligned_alloc", "pvalloc",       "new",
    "new[]",          "operator new",  "operator new[]"};

// StatementMatcher NewMatcher = cxxNewExpr().bind("allocCall");

// TODO: this is partial, it needs more work and testing
// StatementMatcher MakeUniqueMatcher =
//     callExpr(
//         hasDeclaration(functionDecl(
//             matchesName("^(::)?std::make_unique$"))))
//         .bind("allocCall");

static llvm::cl::OptionCategory MyToolCategory("fsan-frontend options");

int main(int argc, const char **argv) {
  auto ExpectedParser = CommonOptionsParser::create(argc, argv, MyToolCategory);
  if (!ExpectedParser) {
    llvm::errs() << "Error creating CommonOptionsParser: "
                 << llvm::toString(ExpectedParser.takeError()) << "\n";
    return 1;
  }
  CommonOptionsParser &OptionsParser = ExpectedParser.get();
  ClangTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());

  MatchFinder Finder;

  StatementMatcher ReferencesToAllocator =
      declRefExpr(
          to(functionDecl(matchesName(
              "^(::)?malloc$|^(::)?calloc$|^(::)?realloc$|^(::)?valloc$|^(::)"
              "?posix_memalign$|^(::)?aligned_alloc$|^(::)?pvalloc$"))))
          .bind("allocCall");

  RewriteRuleWith<std::string> addPrefixToAllocator = makeRule(
      ReferencesToAllocator,
      changeTo(node("allocCall"), run([](const MatchFinder::MatchResult &Result)
                                          -> llvm::Expected<std::string> {
                 const auto *DRE =
                     Result.Nodes.getNodeAs<DeclRefExpr>("allocCall");
                 if (!DRE)
                   return llvm::make_error<llvm::StringError>(
                       "Expected DeclRefExpr bound to 'ref'",
                       llvm::inconvertibleErrorCode());
                 return "typed_" + DRE->getDecl()->getNameAsString();
               })),
      // Wrap the lambda in run() to produce a Generator<std::string>
      clang::transformer::run([](const MatchFinder::MatchResult &Result)
                                  -> llvm::Expected<std::string> {
        const auto *DRE = Result.Nodes.getNodeAs<DeclRefExpr>("allocCall");
        if (!DRE)
          return llvm::make_error<llvm::StringError>(
              "Expected DeclRefExpr bound to 'ref'",
              llvm::inconvertibleErrorCode());
        return "typed_" + DRE->getDecl()->getNameAsString();
      }));

  StatementMatcher AllocatorCall =
      callExpr(
          hasDeclaration(functionDecl(matchesName(
              "^(::)?malloc$|^(::)?calloc$|^(::)?realloc$|^(::)?valloc$|^"
              "(::)?posix_memalign$|^(::)?aligned_alloc$|^(::)?pvalloc$"))))
          .bind("call");

  RewriteRuleWith<std::string> addPrefixToAllocatorAndArgument = makeRule(
      AllocatorCall,
      changeTo(node("call"), run([](const MatchFinder::MatchResult &Result)
                                     -> llvm::Expected<std::string> {
                 const auto *Call = Result.Nodes.getNodeAs<CallExpr>("call");
                 if (!Call)
                   return llvm::make_error<llvm::StringError>(
                       "missing CallExpr", llvm::inconvertibleErrorCode());

                 // Extract the function name by walking through the implicit
                 // cast and UsingShadow to get to the actual FunctionDecl
                 const auto *Callee = Call->getDirectCallee();
                 if (!Callee)
                   return llvm::make_error<llvm::StringError>(
                       "cannot resolve direct callee",
                       llvm::inconvertibleErrorCode());

                 const auto &SM = *Result.SourceManager;
                 const auto &LO = Result.Context->getLangOpts();

                 std::vector<std::string> Args;
                 for (const Expr *Arg : Call->arguments()) {
                   StringRef Text = Lexer::getSourceText(
                       CharSourceRange::getTokenRange(Arg->getSourceRange()),
                       SM, LO);
                   if (Text.empty())
                     return llvm::make_error<llvm::StringError>(
                         "cannot read argument source",
                         llvm::inconvertibleErrorCode());
                   Args.push_back(Text.str());
                 }
                 Args.push_back("0");

                 return "typed_" + Callee->getNameAsString() + "(" +
                        llvm::join(Args, ", ") + ")";
               })),
      clang::transformer::run([](const MatchFinder::MatchResult &Result)
                                  -> llvm::Expected<std::string> {
        const auto *Call = Result.Nodes.getNodeAs<CallExpr>("call");
        if (!Call || !Call->getDirectCallee())
          return llvm::make_error<llvm::StringError>(
              "missing CallExpr", llvm::inconvertibleErrorCode());
        return "typed_" + Call->getDirectCallee()->getNameAsString();
      }));

  // RewriteRuleWith<std::string> addPrefixToAllocatorAndArgument = makeRule(
  //     AllocatorCall,
  //     changeTo(node("call"), run([](const MatchFinder::MatchResult &Result)
  //                                    -> llvm::Expected<std::string> {
  //                const auto *DRE =
  //                    Result.Nodes.getNodeAs<DeclRefExpr>("allocCall");
  //                const auto *Call = Result.Nodes.getNodeAs<CallExpr>("call");
  //                if (!DRE || !Call)
  //                  return llvm::make_error<llvm::StringError>(
  //                      "missing node", llvm::inconvertibleErrorCode());

  //                const auto &SM = *Result.SourceManager;
  //                const auto &LO = Result.Context->getLangOpts();

  //                std::vector<std::string> Args;
  //                for (const Expr *Arg : Call->arguments()) {
  //                  StringRef Text = Lexer::getSourceText(
  //                      CharSourceRange::getTokenRange(Arg->getSourceRange()),
  //                      SM, LO);
  //                  if (Text.empty())
  //                    return llvm::make_error<llvm::StringError>(
  //                        "cannot read argument source",
  //                        llvm::inconvertibleErrorCode());
  //                  Args.push_back(Text.str());
  //                }
  //                Args.push_back("0");

  //                return "typed_" + DRE->getDecl()->getNameAsString() + "(" +
  //                       llvm::join(Args, ", ") + ")";
  //              })),
  //     clang::transformer::run([](const MatchFinder::MatchResult &Result)
  //                                 -> llvm::Expected<std::string> {
  //       const auto *DRE = Result.Nodes.getNodeAs<DeclRefExpr>("allocCall");
  //       if (!DRE)
  //         return llvm::make_error<llvm::StringError>(
  //             "missing node", llvm::inconvertibleErrorCode());
  //       return "typed_" + DRE->getDecl()->getNameAsString();
  //     }));
  // // RULE

  std::map<std::string, std::vector<AtomicChange>> ChangesByFile;

  Transformer SmartAss(
      std::move(addPrefixToAllocatorAndArgument),
      [&ChangesByFile](llvm::Expected<TransformerResult<std::string>> Result) {
        if (!Result) {
          llvm::consumeError(Result.takeError());
        } else {
          llvm::errs() << "Metadata: " << Result->Metadata << "\n";
          // Collect changes grouped by file
          for (auto &Change : Result->Changes) {
            ChangesByFile[Change.getFilePath()].push_back(std::move(Change));
          }
        }
      });

  SmartAss.registerMatchers(&Finder);

  int RC = Tool.run(newFrontendActionFactory(&Finder).get());

  // After matching, apply collected changes to disk
  for (auto &Entry : ChangesByFile) {
    const std::string &FilePath = Entry.first;
    std::vector<AtomicChange> &Changes = Entry.second;

    llvm::ErrorOr<std::unique_ptr<llvm::MemoryBuffer>> BufferOrErr =
        llvm::MemoryBuffer::getFile(FilePath);
    if (!BufferOrErr) {
      llvm::errs() << "Error reading file: " << FilePath << "\n";
      continue;
    }

    llvm::Expected<std::string> NewCodeOrErr =
        applyAtomicChanges(FilePath, (*BufferOrErr)->getBuffer(), Changes,
                           clang::tooling::ApplyChangesSpec());
    if (!NewCodeOrErr) {
      llvm::errs() << "Error applying changes: "
                   << llvm::toString(NewCodeOrErr.takeError()) << "\n";
      continue;
    }

    // Write back to disk
    std::error_code EC;
    llvm::raw_fd_ostream Out(FilePath, EC);
    if (EC) {
      llvm::errs() << "Error writing file: " << EC.message() << "\n";
      continue;
    }
    Out << *NewCodeOrErr;
    llvm::errs() << "Rewrote: " << FilePath << "\n";
  }

  return RC;
}
