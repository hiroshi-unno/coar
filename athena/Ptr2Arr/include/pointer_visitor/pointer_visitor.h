#ifndef POINTER_VISITOR_AND_REWRITER_H
#define POINTER_VISITOR_AND_REWRITER_H

#include "clang/Basic/SourceManager.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/RecursiveASTVisitor.h"

#include "../points_to_analysis/points_to_set.h"

class PointerVisitor : public clang::RecursiveASTVisitor<PointerVisitor> {

public:
    explicit PointerVisitor(clang::ASTContext *Context, clang::Rewriter &TheRewriter, std::vector<PointsToSet>& pointsToSets) : Context(Context), TheRewriter(TheRewriter), pointsToSets(pointsToSets) {}

    bool VisitFieldDecl(clang::FieldDecl *FD);
    bool VisitVarDecl(clang::VarDecl *VD);
    bool VisitCallExpr(clang::CallExpr *CE);

private:
    clang::ASTContext *Context;
    clang::Rewriter &TheRewriter;
    std::vector<PointsToSet>& pointsToSets;
};

#endif //POINTER_VISITOR_AND_REWRITER_H