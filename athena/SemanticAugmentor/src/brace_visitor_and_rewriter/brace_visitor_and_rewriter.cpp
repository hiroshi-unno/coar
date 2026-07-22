#include "../../include/brace_visitor_and_rewriter/brace_visitor_and_rewriter.h"

bool BraceVisitorAndRewriter::VisitIfStmt(clang::IfStmt *IS) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(IS->getBeginLoc())) {
        clang::Stmt *then = IS->getThen();
        if (then && !isa<clang::CompoundStmt>(then)) {
            clang::SourceLocation startLoc = clang::Lexer::getLocForEndOfToken(IS->getRParenLoc(), 0, TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
            clang::SourceLocation endLoc = clang::Lexer::getLocForEndOfToken(then->getEndLoc(), 0, TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
            TheRewriter.InsertText(startLoc, "\n{");
            TheRewriter.InsertTextAfterToken(endLoc, "\n}");
        }
    }
    return true;
}

bool BraceVisitorAndRewriter::VisitForStmt(clang::ForStmt *FS) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(FS->getBeginLoc())) {
        clang::Stmt *body = FS->getBody();
        if (body && !isa<clang::CompoundStmt>(body)) {
            clang::SourceLocation startLoc = clang::Lexer::getLocForEndOfToken(FS->getRParenLoc(), 0, TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
            clang::SourceLocation endLoc = clang::Lexer::getLocForEndOfToken(body->getEndLoc(), 0, TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
            TheRewriter.InsertText(startLoc, "\n{");
            TheRewriter.InsertTextAfterToken(endLoc, "\n}");
        }
    }
    return true;
}

bool BraceVisitorAndRewriter::VisitWhileStmt(clang::WhileStmt *WS) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(WS->getBeginLoc())) {
        clang::Stmt *body = WS->getBody();
        if (body && !isa<clang::CompoundStmt>(body)) {
            clang::SourceLocation startLoc = clang::Lexer::getLocForEndOfToken(WS->getRParenLoc(), 0, TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
            clang::SourceLocation endLoc = clang::Lexer::getLocForEndOfToken(body->getEndLoc(), 0, TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
            TheRewriter.InsertText(startLoc, "\n{");
            TheRewriter.InsertTextAfterToken(endLoc, "\n}");
        }
    }
    return true;
}

bool BraceVisitorAndRewriter::VisitDoStmt(clang::DoStmt *DS) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(DS->getBeginLoc())) {
        clang::Stmt *body = DS->getBody();
        if (body && !isa<clang::CompoundStmt>(body)) {
            clang::SourceLocation startLoc = clang::Lexer::getLocForEndOfToken(DS->getDoLoc(), 0, TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
            clang::SourceLocation endLoc = clang::Lexer::getLocForEndOfToken(body->getEndLoc(), 0, TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
            TheRewriter.InsertText(startLoc, "\n{");
            TheRewriter.InsertTextAfterToken(endLoc, "\n}");
        }
    }
    return true;
}