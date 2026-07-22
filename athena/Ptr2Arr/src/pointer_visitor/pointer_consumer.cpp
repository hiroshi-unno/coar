#include "../../include/pointer_visitor/pointer_consumer.h"

void PointerConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
}