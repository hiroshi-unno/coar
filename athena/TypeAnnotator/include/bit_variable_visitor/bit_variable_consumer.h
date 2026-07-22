#ifndef BIT_VARIABLE_CONSUMER_H
#define BIT_VARIABLE_CONSUMER_H

#include "clang/Frontend/CompilerInstance.h"

#include "bit_variable_visitor.h"

using namespace clang;

class BitVariableConsumer : public clang::ASTConsumer {
public:
    explicit BitVariableConsumer(ASTContext *Context, Rewriter &TheRewriter, std::vector<BitVariable> &bitVariables) : Visitor(Context, TheRewriter, bitVariables), TheRewriter(TheRewriter) {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context);

private:
    BitVariableVisitor Visitor;
    clang::Rewriter &TheRewriter;
};

#endif //BIT_VARIABLE_CONSUMER_H