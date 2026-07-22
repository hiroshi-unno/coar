#ifndef BIT_OPERATION_VISITOR_H
#define BIT_OPERATION_VISITOR_H

#include "clang/Basic/SourceManager.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/RecursiveASTVisitor.h"

class BitOperationVisitor : public clang::RecursiveASTVisitor<BitOperationVisitor> {
public:
    explicit BitOperationVisitor(clang::ASTContext *Context, clang::Rewriter &TheRewriter, bool &hasBitOperation) : Context(Context), TheRewriter(TheRewriter), hasBitOperation(hasBitOperation) {}

    bool VisitBinaryOperator(clang::BinaryOperator *BO);

private:
    clang::ASTContext *Context;
    clang::Rewriter &TheRewriter;
    bool &hasBitOperation;
};

#endif //BIT_OPERATION_VISITOR_H