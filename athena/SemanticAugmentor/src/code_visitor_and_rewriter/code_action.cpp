#include "../../include/code_visitor_and_rewriter/code_action.h"

std::unique_ptr<clang::ASTConsumer> CodeAction::CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    TheRewriter.setSourceMgr(Compiler.getSourceManager(), Compiler.getLangOpts());
    return std::make_unique<CodeConsumer>(&Compiler.getASTContext(), TheRewriter, data);
}