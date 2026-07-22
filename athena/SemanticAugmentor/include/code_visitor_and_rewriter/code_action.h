#ifndef CODE_ACTION_H
#define CODE_ACTION_H

#include "clang/Frontend/FrontendAction.h"

#include "code_consumer.h"

using namespace clang;

class CodeAction : public clang::ASTFrontendAction {
public:
    explicit CodeAction(Data& data) : data(data) {}

    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile);

private:
    clang::Rewriter TheRewriter;
    Data& data;
};

#endif //CODE_ACTION_H