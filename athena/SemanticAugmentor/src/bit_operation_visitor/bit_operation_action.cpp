#include "../../include/bit_operation_visitor/bit_operation_action.h"

std::unique_ptr<clang::ASTConsumer> BitOperationAction::CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    TheRewriter.setSourceMgr(Compiler.getSourceManager(), Compiler.getLangOpts());
    return std::make_unique<BitOperationConsumer>(&Compiler.getASTContext(), TheRewriter, hasBitOperation);
}