set(LLVM_LINK_COMPONENTS
  FrontendOpenMP
  Support
  )

set(CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_MODULE_PATH})
find_package(Filesystem REQUIRED COMPONENTS Final MODULE)

add_clang_executable(openfoam
  openfoam.cpp
  )

clang_target_link_libraries(openfoam
  PRIVATE
  clangAST
  clangASTMatchers
  clangBasic
  clangFrontend
  clangTooling
  clangToolingRefactoring
  std::filesystem
  )

set_target_properties(openfoam PROPERTIES CXX_STANDARD 17)
