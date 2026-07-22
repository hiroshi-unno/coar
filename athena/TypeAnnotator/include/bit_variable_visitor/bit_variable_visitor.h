#ifndef BIT_VARIABLE_VISITOR_H
#define BIT_VARIABLE_VISITOR_H

#include "clang/Basic/SourceManager.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/RecursiveASTVisitor.h"

#include "bit_variable.h"

class BitVariableVisitor : public clang::RecursiveASTVisitor<BitVariableVisitor> {

public:
    explicit BitVariableVisitor(clang::ASTContext *Context, clang::Rewriter &TheRewriter, std::vector<BitVariable> &bitVariables) : Context(Context), TheRewriter(TheRewriter), bitVariables(bitVariables) {}

    bool VisitBinaryOperator(clang::BinaryOperator *BO);
    void LogBitVariables(clang::Expr *expr);

private:
    clang::ASTContext *Context;
    clang::Rewriter &TheRewriter;
    std::vector<BitVariable> &bitVariables;
};

#endif //BIT_VARIABLE_VISITOR_H