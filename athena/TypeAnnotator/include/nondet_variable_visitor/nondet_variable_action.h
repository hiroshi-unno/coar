#ifndef NONDET_VARIABLE_ACTION_H
#define NONDET_VARIABLE_ACTION_H

#include "clang/Frontend/FrontendAction.h"

#include "nondet_variable_consumer.h"

using namespace clang;

class NondetVariableAction : public clang::ASTFrontendAction {
public:
    explicit NondetVariableAction(std::vector<NondetVariable> &nondetVariables) : nondetVariables(nondetVariables) {}

    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile);

private:
    clang::Rewriter TheRewriter;
    std::vector<NondetVariable>& nondetVariables;
};

#endif //NONDET_VARIABLE_ACTION_H