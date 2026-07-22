#ifndef BIT_EXPRESSION_CONSUMER_H
#define BIT_EXPRESSION_CONSUMER_H

#include "clang/Frontend/CompilerInstance.h"

#include "bit_expression_visitor_and_rewriter.h"

using namespace clang;

class BitExpressionConsumer : public clang::ASTConsumer {
public:
    explicit BitExpressionConsumer(ASTContext *Context, Rewriter &TheRewriter) : VisitorAndRewriter(Context, TheRewriter), TheRewriter(TheRewriter) {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context);

private:
    BitExpressionVisitorAndRewriter VisitorAndRewriter;
    clang::Rewriter &TheRewriter;
};

#endif //BIT_EXPRESSION_CONSUMER_H