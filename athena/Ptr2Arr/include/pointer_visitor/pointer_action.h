#ifndef POINTER_ACTION_H
#define POINTER_ACTION_H

#include "clang/Frontend/FrontendAction.h"

#include "pointer_consumer.h"

using namespace clang;

class PointerAction : public clang::ASTFrontendAction {
public:
    explicit PointerAction(std::vector<PointsToSet>& pointsToSets) : pointsToSets(pointsToSets) {}

    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile);

private:
    clang::Rewriter TheRewriter;
    std::vector<PointsToSet>& pointsToSets;
};

#endif //POINTER_ACTION_H