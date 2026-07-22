#include "../../include/nondet_variable_visitor/nondet_variable_action.h"

std::unique_ptr<clang::ASTConsumer> NondetVariableAction::CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    TheRewriter.setSourceMgr(Compiler.getSourceManager(), Compiler.getLangOpts());
    return std::make_unique<NondetVariableConsumer>(&Compiler.getASTContext(), TheRewriter, nondetVariables);
}