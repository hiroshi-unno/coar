#include "../../include/pointer_visitor/pointer_action.h"

std::unique_ptr<clang::ASTConsumer> PointerAction::CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    TheRewriter.setSourceMgr(Compiler.getSourceManager(), Compiler.getLangOpts());
    return std::make_unique<PointerConsumer>(&Compiler.getASTContext(), TheRewriter, pointsToSets);
}