#include "../../include/bit_variable_visitor/bit_variable_consumer.h"

void BitVariableConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
}