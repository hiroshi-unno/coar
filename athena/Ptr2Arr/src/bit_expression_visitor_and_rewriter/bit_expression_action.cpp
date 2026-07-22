#include "../../include/bit_expression_visitor_and_rewriter/bit_expression_action.h"

std::unique_ptr<clang::ASTConsumer> BitExpressionAction::CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    TheRewriter.setSourceMgr(Compiler.getSourceManager(), Compiler.getLangOpts());
    return std::make_unique<BitExpressionConsumer>(&Compiler.getASTContext(), TheRewriter);
}