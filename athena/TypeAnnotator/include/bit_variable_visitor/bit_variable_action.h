#ifndef BIT_VARIABLE_ACTION_H
#define BIT_VARIABLE_ACTION_H

#include "clang/Frontend/FrontendAction.h"

#include "bit_variable_consumer.h"

using namespace clang;

class BitVariableAction : public clang::ASTFrontendAction {
public:
    explicit BitVariableAction(std::vector<BitVariable> &bitVariables) : bitVariables(bitVariables) {}

    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile);

private:
    clang::Rewriter TheRewriter;
    std::vector<BitVariable>& bitVariables;
};

#endif //BIT_VARIABLE_ACTION_H