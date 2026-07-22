#include "../../include/brace_visitor_and_rewriter/brace_action.h"

std::unique_ptr<clang::ASTConsumer> BraceAction::CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    TheRewriter.setSourceMgr(Compiler.getSourceManager(), Compiler.getLangOpts());
    return std::make_unique<BraceConsumer>(&Compiler.getASTContext(), TheRewriter);
}