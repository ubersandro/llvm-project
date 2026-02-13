set( LLVM_LINK_COMPONENTS
  ${LLVM_TARGETS_TO_BUILD}
  Option
  Support
  )

add_clang_tool(fsan-frontend
  FSanFrontend.cpp
  )

clang_target_link_libraries(fsan-frontend
  PRIVATE
  clangAST
  clangBasic
  clangDriver
  clangFrontend
  clangRewriteFrontend
  clangSerialization
  clangStaticAnalyzerFrontend
  clangTooling
  clangToolingSyntax
  clangTransformer
  )
