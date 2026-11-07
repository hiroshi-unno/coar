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

// True when both --memory-safety and --assume-safety are given. The two are exclusive: the first
// makes an out-of-bounds access an error for a safety checker to find, the second makes it the end
// of the execution for a termination checker, and one program cannot do both.
bool safetyModesConflict();

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
    bool VisitReturnStmt(clang::ReturnStmt *RS);
    bool requiresReachErrorDeclaration() const { return reachErrorCallGenerated; }
    // Makes the insertions that must follow every other rewrite (see `deferredInsertions`); called
    // once the traversal is over.
    void applyDeferredInsertions();

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
    // The bounds of the block the pointer value `E` points into, as two expressions (length, base)
    // that are valid once `E` has been evaluated. False when the block cannot be found.
    bool boundsOf(const clang::Expr *E, std::string &len, std::string &base);
    // The name of the function `CE` calls when that function is defined in the main file and
    // returns a pointer, so that its returns record their bounds; empty otherwise.
    std::string trackedReturnName(const clang::CallExpr *CE);
    // Where the memory array of `typeName` must be declared when that type is a struct or union the
    // main file defines after the function definition `first`: right before the next function
    // definition. Invalid when the type is defined before `first`, elsewhere, or is no record.
    clang::SourceLocation laterRecordLocation(const std::string &typeName, const clang::FunctionDecl *first);
    const clang::RecordDecl *lookupRecord(const std::string &typeName);
    // True when `typeName` names a struct or union the translation unit declares and never defines.
    bool undefinedRecord(const std::string &typeName);
    // Insertions to make after the traversal, at a place whose own rewrites come later in it.
    std::vector<std::pair<clang::SourceLocation, std::string>> deferredInsertions;
    bool reachErrorCallGenerated = false;
    bool isPreCheckPhase = false;
    bool hasFreeInCode = false;
};

#endif //CODE_VISITOR_AND_REWRITER_H
