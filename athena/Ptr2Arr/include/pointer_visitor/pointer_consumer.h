#ifndef POINTER_CONSUMER_H
#define POINTER_CONSUMER_H

#include "clang/Frontend/CompilerInstance.h"

#include "pointer_visitor.h"

using namespace clang;

class PointerConsumer : public clang::ASTConsumer {
public:
    explicit PointerConsumer(ASTContext *Context, Rewriter &TheRewriter, std::vector<PointsToSet>& pointsToSets) : Visitor(Context, TheRewriter, pointsToSets), TheRewriter(TheRewriter) {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context);

private:
    PointerVisitor Visitor;
    clang::Rewriter &TheRewriter;
};

#endif //POINTER_CONSUMER_H