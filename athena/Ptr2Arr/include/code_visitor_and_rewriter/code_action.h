#ifndef CODE_ACTION_H
#define CODE_ACTION_H

#include "clang/Frontend/FrontendAction.h"
#include "code_consumer.h"
#include "tracking_rewriter.h"

using namespace clang;

class CodeAction : public clang::ASTFrontendAction {
public:
    explicit CodeAction(std::vector<MemorySet>& memorySets, std::vector<PointsToString>& pointsToStrings, const std::map<std::string, std::vector<std::string>>& functionReturnMap) : memorySets(memorySets), pointsToStrings(pointsToStrings), functionReturnMap(functionReturnMap) {}

    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile);

private:
    clang::Rewriter rewriter_;
    std::vector<MemorySet>& memorySets;
    std::vector<PointsToString>& pointsToStrings;
    const std::map<std::string, std::vector<std::string>>& functionReturnMap;
};

#endif //CODE_ACTION_H