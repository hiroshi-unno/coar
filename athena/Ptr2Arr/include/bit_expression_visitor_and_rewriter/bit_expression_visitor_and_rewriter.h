#ifndef BIT_EXPRESSION_VISITOR_AND_REWRITER_H
#define BIT_EXPRESSION_VISITOR_AND_REWRITER_H

#include <clang/Lex/Lexer.h>
#include "clang/Basic/SourceManager.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/RecursiveASTVisitor.h"

#include "../file_writer/info.h"

class BitExpressionVisitorAndRewriter : public clang::RecursiveASTVisitor<BitExpressionVisitorAndRewriter> {
    int gtvCounter = 0;
    bool isFirstFunction = true;
    clang::SourceLocation firstFunctionStartLoc;

public:
    explicit BitExpressionVisitorAndRewriter(clang::ASTContext *Context, clang::Rewriter &TheRewriter) : Context(Context), TheRewriter(TheRewriter) {}

    bool VisitFunctionDecl(clang::FunctionDecl *FD);
    bool VisitBinaryOperator(clang::BinaryOperator *BO);

private:
    clang::ASTContext *Context;
    clang::Rewriter &TheRewriter;
};

#endif //BIT_EXPRESSION_VISITOR_AND_REWRITER_H