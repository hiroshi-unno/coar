#include "../../include/brace_visitor_and_rewriter/brace_consumer.h"

void BraceConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    VisitorAndRewriter.TraverseDecl(Context.getTranslationUnitDecl());
    std::error_code EC;
    llvm::raw_fd_ostream stream((outputDirectory / (sourceCodeName + "_SemanticAugmentor.c")).string(), EC, llvm::sys::fs::OF_Text);
    TheRewriter.getEditBuffer(TheRewriter.getSourceMgr().getMainFileID()).write(stream);
    stream.close();
}