#ifndef BRACE_VISITOR_AND_REWRITER_H
#define BRACE_VISITOR_AND_REWRITER_H

#include <clang/Lex/Lexer.h>
#include "clang/Basic/SourceManager.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/RecursiveASTVisitor.h"

#include "../info.h"

class BraceVisitorAndRewriter : public clang::RecursiveASTVisitor<BraceVisitorAndRewriter> {

public:
    explicit BraceVisitorAndRewriter(clang::ASTContext *Context, clang::Rewriter &TheRewriter) : Context(Context), TheRewriter(TheRewriter) {}

    bool VisitIfStmt(clang::IfStmt *IS);
    bool VisitForStmt(clang::ForStmt *FS);
    bool VisitWhileStmt(clang::WhileStmt *WS);
    bool VisitDoStmt(clang::DoStmt *DS);

private:
    clang::ASTContext *Context;
    clang::Rewriter &TheRewriter;
};

#endif //BRACE_VISITOR_AND_REWRITER_H