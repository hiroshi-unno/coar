#ifndef BIT_OPERATION_ACTION_H
#define BIT_OPERATION_ACTION_H

#include "clang/Frontend/FrontendAction.h"

#include "bit_operation_consumer.h"

using namespace clang;

class BitOperationAction : public clang::ASTFrontendAction {
public:
    explicit BitOperationAction(bool &hasBitOperation) : hasBitOperation(hasBitOperation) {}

    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile);

private:
    clang::Rewriter TheRewriter;
    bool& hasBitOperation;
};

#endif //BIT_OPERATION_ACTION_H