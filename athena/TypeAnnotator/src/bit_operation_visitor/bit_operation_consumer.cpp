#include "../../include/bit_operation_visitor/bit_operation_consumer.h"

void BitOperationConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
}