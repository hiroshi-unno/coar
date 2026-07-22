#ifndef CODE_VISITOR_AND_REWRITER_H
#define CODE_VISITOR_AND_REWRITER_H

#include <regex>
#include <fstream>
#include <clang/Lex/Lexer.h>
#include "clang/Basic/SourceManager.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/RecursiveASTVisitor.h"

#include "../file_writer/file_writer.h"
#include "../memory_analysis/memory_set.h"
#include "tracking_rewriter.h"
#include "../points_to_analysis/points_to_set.h"

class CodeVisitorAndRewriter : public clang::RecursiveASTVisitor<CodeVisitorAndRewriter> {
    bool isFirstFunction = true;
    std::string currentFunction="";
    clang::SourceLocation mainFunctionStartLoc;
    std::map<std::string, std::string> arrayVariableSizes;

public:
    explicit CodeVisitorAndRewriter(clang::ASTContext *Context, TrackingRewriter &TheRewriter, std::vector<MemorySet>& memorySets, std::vector<PointsToString>& pointsToStrings, const std::map<std::string, std::vector<std::string>>& functionReturnMap)
    : Context(Context), TheRewriter(TheRewriter), memorySets(memorySets), pointsToStrings(pointsToStrings), functionReturnMap(functionReturnMap) {}
    bool shouldTraversePostOrder() const { return true; } // Traverse in post-order to ensure that we process declarations before their uses
    bool TraverseFunctionDecl(clang::FunctionDecl *FD);

    bool VisitFieldDecl(clang::FieldDecl *FD);
    bool VisitFunctionDecl(clang::FunctionDecl *FD);
    bool VisitVarDecl(clang::VarDecl *VD);
    bool VisitDeclRefExpr(clang::DeclRefExpr *DRE);
    bool VisitStringLiteral(clang::StringLiteral *SL);
    bool VisitMemberExpr(clang::MemberExpr *ME);
    bool VisitArraySubscriptExpr(clang::ArraySubscriptExpr *ASE);
    bool VisitBinaryOperator(clang::BinaryOperator *BO);
    bool VisitUnaryOperator(clang::UnaryOperator *UO);
    bool VisitCStyleCastExpr(clang::CStyleCastExpr *CE);
    bool VisitUnaryExprOrTypeTraitExpr(clang::UnaryExprOrTypeTraitExpr *UE);
    bool VisitCallExpr(clang::CallExpr *CE);
    bool TraverseCompoundStmt(clang::CompoundStmt *CS);
    //bool TraverseReturnStmt(clang::ReturnStmt *RS);
    bool requiresReachErrorDeclaration() const { return reachErrorCallGenerated; }

    void runPreCheck(clang::TranslationUnitDecl *TU) {
        this->isPreCheckPhase = true;
        this->hasFreeInCode = false;
        TraverseDecl(TU);
        this->isPreCheckPhase = false;
    }

private:
    clang::ASTContext *Context;
    TrackingRewriter &TheRewriter;
    std::vector<MemorySet>& memorySets;
    std::vector<PointsToString>& pointsToStrings;
    const std::map<std::string, std::vector<std::string>>& functionReturnMap;
    std::set<std::pair<std::string, int>> requiredDecrementHelpers;
    std::set<std::pair<std::string, int>> requiredIncrementHelpers;
    struct AllocInfo {
        std::string varName;
        int memorySetId;
        bool isAlloca;
    };
    std::vector<std::vector<AllocInfo>> scopeStack;
    bool hasReturnStmt = false;
    clang::FunctionDecl *currentFD = nullptr;
    bool reachErrorCallGenerated = false;
    bool isPreCheckPhase = false;
    bool hasFreeInCode = false;
};

#endif //CODE_VISITOR_AND_REWRITER_H
