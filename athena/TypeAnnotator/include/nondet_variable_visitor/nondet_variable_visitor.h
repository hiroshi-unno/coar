#ifndef NONDET_VARIABLE_VISITOR_H
#define NONDET_VARIABLE_VISITOR_H

#include "clang/Lex/Lexer.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/RecursiveASTVisitor.h"

#include "nondet_variable.h"

class NondetVariableVisitor : public clang::RecursiveASTVisitor<NondetVariableVisitor> {

public:
    explicit NondetVariableVisitor(clang::ASTContext *Context, clang::Rewriter &TheRewriter, std::vector<NondetVariable> &nondetVariables) : Context(Context), TheRewriter(TheRewriter), nondetVariables(nondetVariables) {}

    bool VisitVarDecl(clang::VarDecl *VD);
    bool VisitBinaryOperator(clang::BinaryOperator *BO);

private:
    clang::ASTContext *Context;
    clang::Rewriter &TheRewriter;
    std::vector<NondetVariable> &nondetVariables;
};

#endif //NONDET_VARIABLE_VISITOR_H