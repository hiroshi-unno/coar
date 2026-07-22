#ifndef BIT_EXPRESSION_ACTION_H
#define BIT_EXPRESSION_ACTION_H

#include "clang/Frontend/FrontendAction.h"

#include "bit_expression_consumer.h"

using namespace clang;

class BitExpressionAction : public clang::ASTFrontendAction {
public:
    explicit BitExpressionAction() {}

    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile);

private:
    clang::Rewriter TheRewriter;
};

#endif //BIT_EXPRESSION_ACTION_H