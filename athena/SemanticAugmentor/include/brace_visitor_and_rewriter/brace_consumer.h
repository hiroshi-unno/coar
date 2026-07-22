#ifndef BRACE_CONSUMER_H
#define BRACE_CONSUMER_H

#include "clang/Frontend/CompilerInstance.h"

#include "brace_visitor_and_rewriter.h"

using namespace clang;

class BraceConsumer : public clang::ASTConsumer {
public:
    explicit BraceConsumer(ASTContext *Context, Rewriter &TheRewriter) : VisitorAndRewriter(Context, TheRewriter), TheRewriter(TheRewriter) {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context);

private:
    BraceVisitorAndRewriter VisitorAndRewriter;
    clang::Rewriter &TheRewriter;
};

#endif //BRACE_CONSUMER_H