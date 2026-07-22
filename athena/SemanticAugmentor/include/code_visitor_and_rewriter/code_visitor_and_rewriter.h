#ifndef CODE_VISITOR_AND_REWRITER_H
#define CODE_VISITOR_AND_REWRITER_H

#include <set>
#include <regex>
#include <fstream>
#include <sstream>
#include <clang/Lex/Lexer.h>
#include "clang/Basic/SourceManager.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/RecursiveASTVisitor.h"

#include "../info.h"
#include "../data_parser/data.h"

class CodeVisitorAndRewriter : public clang::RecursiveASTVisitor<CodeVisitorAndRewriter> {
    bool isFirstFunction = true;
    std::string currentFunction;
    std::set<unsigned int> modifiedLines;

public:
    explicit CodeVisitorAndRewriter(clang::ASTContext *Context, clang::Rewriter &TheRewriter, Data& data) : Context(Context), TheRewriter(TheRewriter), data(data) {}

    bool VisitFieldDecl(clang::FieldDecl *FD);
    bool VisitFunctionDecl(clang::FunctionDecl *FD);
    bool VisitVarDecl(clang::VarDecl *VD);
    bool VisitCallExpr(clang::CallExpr *CE);
    bool VisitUnaryOperator(clang::UnaryOperator *UO);
    bool VisitBinaryOperator(clang::BinaryOperator *BO);
    bool VisitIfStmt(clang::IfStmt *IS);
    bool VisitForStmt(clang::ForStmt *FS);
    bool VisitWhileStmt(clang::WhileStmt *WS);
    bool VisitDoStmt(clang::DoStmt *DS);
    bool VisitReturnStmt(clang::ReturnStmt *RS);

    void HandleCondition1(clang::Expr *expr);
    void HandleCondition2(clang::Expr *expr, clang::SourceLocation startLoc, clang::SourceLocation endLoc);
    bool HasMatchingData(clang::Expr *expr);

private:
    clang::ASTContext *Context;
    clang::Rewriter &TheRewriter;
    Data& data;
};

#endif //CODE_VISITOR_AND_REWRITER_H