#include "../../include/bit_expression_visitor_and_rewriter/bit_expression_consumer.h"

void BitExpressionConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    VisitorAndRewriter.TraverseDecl(Context.getTranslationUnitDecl());
    std::error_code EC;
    llvm::raw_fd_ostream stream(outputSourcePath.string(), EC, llvm::sys::fs::OF_Text);
    TheRewriter.getEditBuffer(TheRewriter.getSourceMgr().getMainFileID()).write(stream);
    stream.close();
}