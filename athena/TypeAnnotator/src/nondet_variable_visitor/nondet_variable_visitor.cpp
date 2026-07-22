#include "../../include/nondet_variable_visitor/nondet_variable_visitor.h"

bool NondetVariableVisitor::VisitVarDecl(clang::VarDecl *VD) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(VD->getBeginLoc())) {
        if (VD->hasInit()) {
            if (auto *call = llvm::dyn_cast<clang::CallExpr>(VD->getInit()->IgnoreParenImpCasts())) {
                if (auto *callee = call->getDirectCallee()) {
                    std::string functionName = callee->getNameAsString();
                    if (functionName.find("__VERIFIER_nondet_") == 0) {
                        std::string varName = VD->getNameAsString();
                        unsigned int varDeclLine = SM.getSpellingLineNumber(VD->getLocation());
                        std::string bitwidth, signedness;
                        clang::QualType type = VD->getType();
                        if (auto *BT = type->getAs<clang::BuiltinType>()) {
                            switch (BT->getKind()) {
                                case clang::BuiltinType::UChar:
                                case clang::BuiltinType::Char_U:
                                    bitwidth = "8";
                                    signedness = "unsigned";
                                    break;
                                case clang::BuiltinType::SChar:
                                case clang::BuiltinType::Char_S:
                                    bitwidth = "8";
                                    signedness = "signed";
                                    break;
                                case clang::BuiltinType::UShort:
                                    bitwidth = "16";
                                    signedness = "unsigned";
                                    break;
                                case clang::BuiltinType::Short:
                                    bitwidth = "16";
                                    signedness = "signed";
                                    break;
                                case clang::BuiltinType::UInt:
                                    bitwidth = "32";
                                    signedness = "unsigned";
                                    break;
                                case clang::BuiltinType::Int:
                                    bitwidth = "32";
                                    signedness = "signed";
                                    break;
                                case clang::BuiltinType::ULong:
                                    bitwidth = "64";
                                    signedness = "unsigned";
                                    break;
                                case clang::BuiltinType::Long:
                                    bitwidth = "64";
                                    signedness = "signed";
                                    break;
                                default:
                                    return true;
                            }
                        }
                        nondetVariables.push_back({varName, varDeclLine, bitwidth, signedness});
                    }
                }
            }
        }
    }
    return true;
}


bool NondetVariableVisitor::VisitBinaryOperator(clang::BinaryOperator *BO) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(BO->getBeginLoc())) {
        clang::Expr *leftExpr = BO->getLHS()->IgnoreParenImpCasts();

        if (auto *call = llvm::dyn_cast<clang::CallExpr>(BO->getRHS()->IgnoreParenImpCasts())) {
            if (auto *callee = call->getDirectCallee()) {
                std::string functionName = callee->getNameAsString();
                if (functionName.find("__VERIFIER_nondet_") == 0) {
                    std::string varName = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(leftExpr->getSourceRange()), SM, TheRewriter.getLangOpts()).str();
                    unsigned int varDeclLine = SM.getSpellingLineNumber(leftExpr->getExprLoc());
                    std::string bitwidth, signedness;
                    std::string type = functionName.substr(strlen("__VERIFIER_nondet_"));
                    if (type == "uchar") {
                        bitwidth = "8";
                        signedness = "unsigned";
                    }
                    else if (type == "char") {
                        bitwidth = "8";
                        signedness = "signed";
                    }
                    else if (type == "ushort") {
                        bitwidth = "16";
                        signedness = "unsigned";
                    }
                    else if (type == "short") {
                        bitwidth = "16";
                        signedness = "signed";
                    }
                    else if (type == "uint") {
                        bitwidth = "32";
                        signedness = "unsigned";
                    }
                    else if (type == "int") {
                        bitwidth = "32";
                        signedness = "signed";
                    }
                    else if (type == "ulong") {
                        bitwidth = "64";
                        signedness = "unsigned";
                    }
                    else if (type == "long") {
                        bitwidth = "64";
                        signedness = "signed";
                    }
                    nondetVariables.push_back({varName, varDeclLine, bitwidth, signedness});
                }
            }
        }
    }
    return true;
}