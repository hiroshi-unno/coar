#include "../../include/nondet_variable_visitor/nondet_variable_consumer.h"

void NondetVariableConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
}