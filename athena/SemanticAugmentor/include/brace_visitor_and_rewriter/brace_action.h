#ifndef BRACE_ACTION_H
#define BRACE_ACTION_H

#include "clang/Frontend/FrontendAction.h"

#include "brace_consumer.h"

using namespace clang;

class BraceAction : public clang::ASTFrontendAction {
public:
    explicit BraceAction() {}

    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile);

private:
    clang::Rewriter TheRewriter;
};

#endif //BRACE_ACTION_H