#include "../../include/bit_variable_visitor/bit_variable_action.h"

std::unique_ptr<clang::ASTConsumer> BitVariableAction::CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    TheRewriter.setSourceMgr(Compiler.getSourceManager(), Compiler.getLangOpts());
    return std::make_unique<BitVariableConsumer>(&Compiler.getASTContext(), TheRewriter, bitVariables);
}