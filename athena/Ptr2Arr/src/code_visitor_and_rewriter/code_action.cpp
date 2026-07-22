#include "../../include/code_visitor_and_rewriter/code_action.h"

std::unique_ptr<clang::ASTConsumer> CodeAction::CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    rewriter_.setSourceMgr(Compiler.getSourceManager(), Compiler.getLangOpts());
    auto trackingRewriter = std::make_unique<TrackingRewriter>(rewriter_);
    return std::make_unique<CodeConsumer>(&Compiler.getASTContext(), std::move(trackingRewriter), memorySets, pointsToStrings, functionReturnMap);
}