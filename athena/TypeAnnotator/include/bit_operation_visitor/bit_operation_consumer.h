#ifndef BIT_OPERATION_CONSUMER_H
#define BIT_OPERATION_CONSUMER_H

#include "clang/Frontend/CompilerInstance.h"

#include "bit_operation_visitor.h"

using namespace clang;

class BitOperationConsumer : public clang::ASTConsumer {
public:
    explicit BitOperationConsumer(ASTContext *Context, Rewriter &TheRewriter, bool &hasBitOperation) : Visitor(Context, TheRewriter, hasBitOperation), TheRewriter(TheRewriter) {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context);

private:
    BitOperationVisitor Visitor;
    clang::Rewriter &TheRewriter;
};

#endif //BIT_OPERATION_CONSUMER_H