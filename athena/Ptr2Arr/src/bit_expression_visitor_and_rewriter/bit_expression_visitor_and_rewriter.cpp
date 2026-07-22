#include "../../include/bit_expression_visitor_and_rewriter/bit_expression_visitor_and_rewriter.h"

bool BitExpressionVisitorAndRewriter::VisitFunctionDecl(clang::FunctionDecl *FD) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(FD->getBeginLoc())) {
        if (FD->hasBody() && isFirstFunction) {
            firstFunctionStartLoc = FD->getBeginLoc();
            isFirstFunction = false;
        }
    }
    return true;
}

bool BitExpressionVisitorAndRewriter::VisitBinaryOperator(clang::BinaryOperator *BO) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(BO->getBeginLoc())) {
        if (BO->isBitwiseOp() || BO->isShiftOp()) {
            //E1 op E2 where op ∈ {&, |, ^, <<, >>}
            clang::Expr *leftExpr = BO->getLHS()->IgnoreParenImpCasts();
            if (dyn_cast<clang::BinaryOperator>(leftExpr)) {
                std::string varName = "gtv_" + std::to_string(gtvCounter);

                clang::SourceRange leftExprRange = leftExpr->getSourceRange();
                std::string leftExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(leftExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                std::string textToInsert = leftExpr->getType().getAsString() + " " + varName + ";\n";
                TheRewriter.InsertTextBefore(firstFunctionStartLoc, textToInsert);

                std::string textToReplace = "(" + varName + " = " + leftExprStr + ")";
                TheRewriter.ReplaceText(leftExpr->getSourceRange(), textToReplace);

                gtvCounter = gtvCounter + 1;
            }

            clang::Expr *rightExpr = BO->getRHS()->IgnoreParenImpCasts();
            if (dyn_cast<clang::BinaryOperator>(rightExpr)) {
                std::string varName = "gtv_" + std::to_string(gtvCounter);

                clang::SourceRange rightExprRange = rightExpr->getSourceRange();
                std::string rightExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(rightExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                std::string textToInsert = rightExpr->getType().getAsString() + " " + varName + ";\n";
                TheRewriter.InsertTextBefore(firstFunctionStartLoc, textToInsert);

                std::string textToReplace = "(" + varName + " = " + rightExprStr + ")";
                TheRewriter.ReplaceText(rightExpr->getSourceRange(), textToReplace);

                gtvCounter = gtvCounter + 1;
            }
        }
    }
    return true;
}