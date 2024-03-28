//===---- tools/extra/openfoam.cpp - Tool to extract OpenFOAMs API ----===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file implements an empty refactoring tool using the clang tooling.
//  The goal is to lower the "barrier to entry" for writing refactoring tools.
//
//  Usage:
//  openfoam <cmake-output-dir> <file1> <file2> ...
//
//  Where <cmake-output-dir> is a CMake build directory in which a file named
//  compile_commands.json exists (enable -DCMAKE_EXPORT_COMPILE_COMMANDS in
//  CMake to get this output).
//
//  <file1> ... specify the paths of files in the CMake source tree. This path
//  is looked up in the compile command database. If the path of a file is
//  absolute, it needs to point into CMake's source tree. If the path is
//  relative, the current working directory needs to be in the CMake source
//  tree and the file must be in a subdirectory of the current working
//  directory. "./" prefixes in the relative files will be automatically
//  removed, but the rest of a relative path must be a suffix of a path in
//  the compile command line database.
//
//  For example, to use tool-template on all files in a subtree of the
//  source tree, use:
//
//    /path/in/subtree $ find . -name '*.cpp'|
//        xargs tool-template /path/to/build
//
//===----------------------------------------------------------------------===//

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Lex/Lexer.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Execution.h"
#include "clang/Tooling/Refactoring.h"
#include "clang/Tooling/Refactoring/AtomicChange.h"
#include "clang/Tooling/StandaloneExecution.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Signals.h"

#include <filesystem>
#include <numeric>
#include <sstream>

using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::tooling;
using namespace llvm;
namespace fs = std::filesystem;

namespace {

// Set up the command line options
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);
static cl::extrahelp ToolHelp(
    R"(This tool creates a JSON file containing the API for the given source files.
The json contains dicts for the function, CXX class, or variable declarations
that are referenced in the source files. Each entry of the dicts consists of the
name (the key) of the declaration, and the file containing it.
)");
static cl::OptionCategory ToolOpenfoamCategory("tool-openfoam options");

static cl::opt<std::string>
    Root("root", cl::desc("The root directory that will be removed from paths"),
         cl::initializer(fs::current_path().string()),
         cl::cat(ToolOpenfoamCategory));

static cl::opt<std::string> FilterDirsOpt(
    "filter-dirs",
    cl::desc("A semi-colon separated list of root directory to filter the AST"),
    cl::cat(ToolOpenfoamCategory));

static cl::opt<std::string>
    Namespace("namespace",
              cl::desc("The namespace that contains the declarations"),
              cl::cat(ToolOpenfoamCategory));

static cl::opt<std::string> NamespaceIgnore(
    "namespace-ignore",
    cl::desc("A namespace that should be ignored (for example 'detail')"),
    cl::cat(ToolOpenfoamCategory));

static cl::opt<bool> EnableTrueLocationFilter(
    "true-location-filter",
    cl::desc("Filter files based on their true directory, following symlinks"),
    cl::initializer(true), cl::cat(ToolOpenfoamCategory));

class ToolTemplateCallback : public MatchFinder::MatchCallback {
public:
  ToolTemplateCallback(json::Object *Map, fs::path RootPath,
                       const std::vector<fs::path> &FilterDirs)
      : Map(Map), RootPath(RootPath), FilterDirs(FilterDirs) {}

  void run(const MatchFinder::MatchResult &Result) override {
    auto *D = Result.Nodes.getNodeAs<Decl>("decl");
    assert(D);

    // skip matches if they don't have a valid source location or if they
    // contain the `::Detail` namespace
    if (!D->getBeginLoc().isValid()) {
      return;
    }
    auto PresumedLoc = Result.SourceManager->getPresumedLoc(D->getBeginLoc());
    auto FilePath = fs::absolute(PresumedLoc.getFilename());

    if (EnableTrueLocationFilter.getValue()) {
      // skip match, if the file containing the match is not a direct descendent
      // of any provided directories.
      if (std::all_of(
              std::begin(FilterDirs), std::end(FilterDirs), [&](const auto &P) {
                auto RelPath = fs::relative(FilePath, P).string();
                auto Length = RelPath.size();
                return Length >= 2 && RelPath[0] == '.' && RelPath[1] == '.';
              })) {
        return;
      }
    }

    json::Object *Path;
    if (auto *T = Result.Nodes.getNodeAs<RecordDecl>("decl")) {
      Path = Map->get("types")->getAsObject();
    } else if (auto *T = Result.Nodes.getNodeAs<FunctionDecl>("decl")) {
      Path = Map->get("functions")->getAsObject();
    } else if (auto *T = Result.Nodes.getNodeAs<VarDecl>("decl")) {
      Path = Map->get("variables")->getAsObject();
    } else {
      return;
    }

    if (auto *TS =
            Result.Nodes.getNodeAs<ClassTemplateSpecializationDecl>("decl")) {
      Path = Path->get("specializations")->getAsObject();
    }

    auto Name = getName(Result);
    Path->try_emplace(Name, fs::relative(FilePath, RootPath));
  }

private:
  std::string getName(const MatchFinder::MatchResult &Result) const {
    auto *TS = Result.Nodes.getNodeAs<ClassTemplateSpecializationDecl>("decl");
    if (TS) {
      std::string TemplateArgs;
      const auto &TemplateArgsList = TS->getTemplateArgs();
      for (size_t i = 0; i < TemplateArgsList.size(); ++i) {
        const auto &CurArg = TemplateArgsList[i];
        if (CurArg.getKind() == TemplateArgument::Type) {
          TemplateArgs.append(CurArg.getAsType().getAsString());

          if (i < TemplateArgsList.size() - 1) {
            TemplateArgs.append(", ");
          }
        }
      }
      return TS->getQualifiedNameAsString() + "<" + TemplateArgs + ">";
    }

    auto *T = Result.Nodes.getNodeAs<TemplateDecl>("decl");
    if (T) {
      std::string TemplateArgs;
      const auto &TemplateArgsList = T->getTemplateParameters()->asArray();
      for (size_t i = 0; i < TemplateArgsList.size(); ++i) {
        auto *CurArg = TemplateArgsList[i];
        TemplateArgs.append(CurArg->getQualifiedNameAsString());

        if (i < TemplateArgsList.size() - 1) {
          TemplateArgs.append(", ");
        }
      }
      return T->getQualifiedNameAsString() + "<" + TemplateArgs + ">";
    }

    auto *D = Result.Nodes.getNodeAs<NamedDecl>("decl");
    assert(D);
    return D->getQualifiedNameAsString();
  }

  json::Object *Map;
  fs::path RootPath;
  const std::vector<fs::path> &FilterDirs;
};
} // end anonymous namespace

int main(int argc, const char **argv) {
  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);

  auto ExpectedParser =
      CommonOptionsParser::create(argc, argv, ToolOpenfoamCategory);
  if (!ExpectedParser) {
    llvm::errs() << ExpectedParser.takeError();
    return 1;
  }
  CommonOptionsParser &OptionsParser = ExpectedParser.get();
  StandaloneToolExecutor Tool(OptionsParser.getCompilations(),
                              OptionsParser.getSourcePathList());

  std::vector<fs::path> FilterDirs;
  std::istringstream ISS(FilterDirsOpt);
  std::string Token;
  while (std::getline(ISS, Token, ';')) {
    FilterDirs.push_back(fs::absolute(Token));
  }

  fs::path RootPath = fs::absolute(Root.getValue());

  json::Object JO;
  JO["types"] = json::Object({{"specializations", json::Object()}});
  JO["functions"] = json::Object({{"specializations", json::Object()}});
  JO["variables"] = json::Object();

  ast_matchers::MatchFinder Finder;
  ToolTemplateCallback Callback(&JO, RootPath, FilterDirs);

  auto AddMatcher = [&](const auto &Regex) {
    llvm::errs() << Regex << "\n";
    Finder.addMatcher(
        namedDecl(isExpansionInFileMatching(Regex),
                  hasAncestor(namespaceDecl(hasName(Namespace.getValue()))),
                  unless(hasAncestor(
                      namespaceDecl(hasName(NamespaceIgnore.getValue())))),
                  anyOf(cxxRecordDecl(hasDefinition(),
                                      unless(hasAncestor(cxxRecordDecl())),
                                      unless(isTemplateInstantiation())),
                        functionDecl(unless(cxxMethodDecl())),
                        varDecl(unless(hasAncestor(cxxRecordDecl())),
                                unless(hasAncestor(functionDecl())))))
            .bind("decl"),
        &Callback);
  };

  if (EnableTrueLocationFilter.getValue()) {
    std::string Regex = "\\.H$";
    AddMatcher(Regex);
  } else {
    for (auto &Dir : FilterDirs) {
      // don't use regex to filter the matches except for the extension
      // add one matcher per header file
      for (auto &DirEntry :
           fs::recursive_directory_iterator(fs::absolute(Dir))) {
        std::string Regex = "/" + DirEntry.path().stem().string() + "\\.H$";
        AddMatcher(Regex);
      }
    }
  }

  auto Err = Tool.execute(newFrontendActionFactory(&Finder));
  if (Err) {
    llvm::errs() << llvm::toString(std::move(Err)) << "\n";
  }

  llvm::outs() << formatv("{0:2}", json::Value(std::move(JO)));
}
