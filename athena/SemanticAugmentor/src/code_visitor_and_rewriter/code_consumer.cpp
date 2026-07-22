#include "../../include/code_visitor_and_rewriter/code_consumer.h"

void CodeConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    VisitorAndRewriter.TraverseDecl(Context.getTranslationUnitDecl());
    std::error_code EC;
    llvm::raw_fd_ostream stream((outputDirectory / (sourceCodeName + "_SemanticAugmentor.c")).string(), EC, llvm::sys::fs::OF_Text);
    TheRewriter.getEditBuffer(TheRewriter.getSourceMgr().getMainFileID()).write(stream);
    stream.close();

    std::fstream cFile(outputDirectory / (sourceCodeName + "_SemanticAugmentor.c"), std::ios::in | std::ios::out);
    std::ostringstream cBuffer;
    cBuffer << cFile.rdbuf();
    cFile.seekp(0);
    cFile << "#include <limits.h>\n#include <stdint.h>\n" << cBuffer.str();
    cFile.close();
}