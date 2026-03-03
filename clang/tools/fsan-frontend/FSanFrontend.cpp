// #include "lib.hpp"
// static llvm::cl::OptionCategory FSanFECategory("fsan-frontend options");

/**
 * FSan frontend based on Libtooling for rewriting mallocs.
 * This plugin is intended to be used with the FSan runtime to type C code.
 * - Typing strategy for C-like allocators: malloc(...) becomes
 * typed_malloc(..., "type"), where "type" is the type of the pointer being
 * allocated.
 * - Typing strategy for C++-like allocators: new T(...) becomes
 * typed_new<T>(..., "type"), where "type" is the type of the pointer being
 * allocated with all the generics info in place.
 *
 */



// std::set<std::string> AllocatingFunctions = {
//     "malloc",         "calloc",        "realloc",       "valloc",
//     "posix_memalign", "aligned_alloc", "pvalloc",       "new",
//     "new[]",          "operator new",  "operator new[]"};

int main(int argc, const char **argv) {
  // auto ExpectedParser = CommonOptionsParser::create(argc, argv, FSanFECategory);
  // if (!ExpectedParser) {
  //   llvm::errs() << "Error creating CommonOptionsParser: "
  //                << llvm::toString(ExpectedParser.takeError()) << "\n";
  //   return 1;
  // }
  // CommonOptionsParser &OptionsParser = ExpectedParser.get();
  // ClangTool Tool(OptionsParser.getCompilations(),
  //                OptionsParser.getSourcePathList());

  // MatchFinder Finder;

  // // this kinda works for simple sizeof

  // // TODO: group rules to decide order, after everything is decorated, run ONE
  // // transformer

  // DebugPrinter AllocCallDebugger;
  // AllocatorCallPrinter AllocCallPrinter;

  // Finder.addMatcher(AllocatorCallWithSizeOfArgumentAndCast, &AllocCallDebugger);
  // Finder.addMatcher(ReferencesToAllocator, &AllocCallPrinter);

  // RewriteRuleWith<std::string> addPrefixToAllocatorAndArgument = makeRule(
  //     AllocatorCallWithSizeOfArgumentAndCast,
  //     changeTo(node("call"), run([](const MatchFinder::MatchResult &Result)
  //                                    -> llvm::Expected<std::string> {
  //                std::string typeStr = "dummy_type";
  //                QualType AllocType;
  //                // NOTE: -1 means reconstruction did not happen
  //                uint64_t arraySize = -1;

  //                const auto *Call = Result.Nodes.getNodeAs<CallExpr>("call");
  //                if (!Call)
  //                  return llvm::make_error<llvm::StringError>(
  //                      "missing CallExpr", llvm::inconvertibleErrorCode());

  //                const auto *Cast = Result.Nodes.getNodeAs<CastExpr>("cast");
  //                const auto *SizeOf =
  //                    Result.Nodes.getNodeAs<UnaryExprOrTypeTraitExpr>("sizeof");

  //                // TODO: assignment, but it might not be necessary
  //                // const auto *
  //                //     FromAssignment; // =
  //                // Result.Nodes.getNodeAs<BinaryOperator>("assignment");

  //                // PROBLEM: cast does not give you size, so recon must happen
  //                // at IR based on type size and allocation size
  //                if (SizeOf) {
  //                  const Expr *CountExpr = nullptr;
  //                  const QualType *FromSizeOf =
  //                      Result.Nodes.getNodeAs<QualType>("sizeofType");
  //                  if (!FromSizeOf)
  //                    return llvm::make_error<llvm::StringError>(
  //                        "missing sizeof type", llvm::inconvertibleErrorCode());
  //                  typeStr = FromSizeOf->getAsString();
  //                  auto *SIZEOFMUL =
  //                      Result.Nodes.getNodeAs<BinaryOperator>("sizeofMul");
  //                  if (!SIZEOFMUL) {
  //                    // TODO: is this sufficient? What if there is a sum? Can
  //                    // this happen? LATER
  //                    arraySize = 1;
  //                  }

  //                  else {
  //                    const Expr *LHS = SIZEOFMUL->getLHS()->IgnoreImpCasts();
  //                    const Expr *RHS = SIZEOFMUL->getRHS()->IgnoreImpCasts();
  //                    if (llvm::isa<UnaryExprOrTypeTraitExpr>(LHS))
  //                      CountExpr = RHS; // sizeof on left, count on right
  //                    else
  //                      CountExpr = LHS; // sizeof on right, count on left

  //                    // Also strip casts from the count itself
  //                    CountExpr = CountExpr->IgnoreImpCasts();

  //                    // Now extract the integer literal
  //                    if (const auto *IL =
  //                            llvm::dyn_cast<IntegerLiteral>(CountExpr)) {
  //                      arraySize = IL->getValue().getZExtValue();

  //                    } else {
  //                      // TODO: in this case, replace it with div?
  //                      arraySize = -1;
  //                    }
  //                  } // there is a SIZEOFMUL
  //                } // if SizeOf

  //                else if (Cast) {
  //                  // no size of, but you have a cast
  //                  AllocType = Cast->getType();
  //                  typeStr = AllocType.getAsString();
  //                  arraySize = -1;
  //                } // if Cast

  //                else {
  //                  // TODO: handle assignment here
  //                }

  //                // Extract the function name by walking through the implicit
  //                // cast and UsingShadow to get to the actual FunctionDecl
  //                const auto *Callee = Call->getDirectCallee();
  //                if (!Callee)
  //                  return llvm::make_error<llvm::StringError>(
  //                      "cannot resolve direct callee",
  //                      llvm::inconvertibleErrorCode());

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
  //                Args.push_back("\"" + typeStr + "\"");

  //                Args.push_back("0x" + llvm::utohexstr(arraySize));

  //                return "typed_" + Callee->getNameAsString() + "(" +
  //                       llvm::join(Args, ", ") + ")";
  //              } // lambda
  //                                )),
  //     clang::transformer::run([](const MatchFinder::MatchResult &Result)
  //                                 -> llvm::Expected<std::string> {
  //       const auto *Call = Result.Nodes.getNodeAs<CallExpr>("call");
  //       if (!Call || !Call->getDirectCallee())
  //         return llvm::make_error<llvm::StringError>(
  //             "missing CallExpr", llvm::inconvertibleErrorCode());
  //       return "typed_" + Call->getDirectCallee()->getNameAsString();
  //     }));

  // std::map<std::string, std::vector<AtomicChange>> ChangesByFile;

  // Transformer SmartAss(
  //     std::move(addPrefixToAllocatorAndArgument),
  //     [&ChangesByFile](llvm::Expected<TransformerResult<std::string>> Result) {
  //       if (!Result) {
  //         llvm::consumeError(Result.takeError());
  //       } else {
  //         llvm::errs() << "Metadata: " << Result->Metadata << "\n";
  //         // Collect changes grouped by file
  //         for (auto &Change : Result->Changes) {
  //           ChangesByFile[Change.getFilePath()].push_back(std::move(Change));
  //         }
  //       }
  //     });

  // // SmartAss.registerMatchers(&Finder);

  // int RC = Tool.run(newFrontendActionFactory(&Finder).get());

  // // After matching, apply collected changes to disk
  // for (auto &Entry : ChangesByFile) {
  //   const std::string &FilePath = Entry.first;
  //   std::vector<AtomicChange> &Changes = Entry.second;

  //   llvm::ErrorOr<std::unique_ptr<llvm::MemoryBuffer>> BufferOrErr =
  //       llvm::MemoryBuffer::getFile(FilePath);
  //   if (!BufferOrErr) {
  //     llvm::errs() << "Error reading file: " << FilePath << "\n";
  //     continue;
  //   }

  //   llvm::Expected<std::string> NewCodeOrErr =
  //       applyAtomicChanges(FilePath, (*BufferOrErr)->getBuffer(), Changes,
  //                          clang::tooling::ApplyChangesSpec());
  //   if (!NewCodeOrErr) {
  //     llvm::errs() << "Error applying changes: "
  //                  << llvm::toString(NewCodeOrErr.takeError()) << "\n";
  //     continue;
  //   }
  //   std::error_code EC;
  //   llvm::raw_fd_ostream Out(FilePath, EC);
  //   if (EC) {
  //     llvm::errs() << "Error writing file: " << EC.message() << "\n";
  //     continue;
  //   }
  //   Out << *NewCodeOrErr;
  //   llvm::errs() << "Rewrote: " << FilePath << "\n";
  // }

  // return RC;
}
