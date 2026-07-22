#ifndef NONDET_VARIABLE_CONSUMER_H
#define NONDET_VARIABLE_CONSUMER_H

#include "clang/Frontend/CompilerInstance.h"

#include "nondet_variable_visitor.h"

using namespace clang;

class NondetVariableConsumer : public clang::ASTConsumer {
public:
    explicit NondetVariableConsumer(ASTContext *Context, Rewriter &TheRewriter, std::vector<NondetVariable> &nondetVariables) : Visitor(Context, TheRewriter, nondetVariables), TheRewriter(TheRewriter) {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context);

private:
    NondetVariableVisitor Visitor;
    clang::Rewriter &TheRewriter;
};

#endif //NONDET_VARIABLE_CONSUMER_H