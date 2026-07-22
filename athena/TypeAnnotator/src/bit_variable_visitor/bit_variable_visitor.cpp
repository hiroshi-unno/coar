#include "../../include/bit_variable_visitor/bit_variable_visitor.h"

bool BitVariableVisitor::VisitBinaryOperator(clang::BinaryOperator *BO) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(BO->getBeginLoc())) {
        if (BO->isAssignmentOp()) {
            if (BO->getOpcode() == clang::BO_Assign) {
            }
            else {
                clang::BinaryOperatorKind opKind = BO->getOpcode();
                if (opKind == clang::BO_AddAssign || opKind == clang::BO_SubAssign || opKind == clang::BO_MulAssign || opKind == clang::BO_DivAssign || opKind == clang::BO_RemAssign) {
                }
                else if (opKind == clang::BO_AndAssign || opKind == clang::BO_OrAssign || opKind == clang::BO_XorAssign || opKind == clang::BO_ShlAssign || opKind == clang::BO_ShrAssign) {
                    //V op= E; where op ∈ {&, |, ^, <<, >>}
                    LogBitVariables(BO->getLHS()->IgnoreParenImpCasts());
                    LogBitVariables(BO->getRHS()->IgnoreParenImpCasts());
                }
            }
        }
        else if (BO->isBitwiseOp() || BO->isShiftOp()) {
            //E1 op E2 where op ∈ {&, |, ^, <<, >>}
            LogBitVariables(BO->getLHS()->IgnoreParenImpCasts());
            LogBitVariables(BO->getRHS()->IgnoreParenImpCasts());
        }
    }
    return true;
}

void BitVariableVisitor::LogBitVariables(clang::Expr *expr) {
    if (clang::DeclRefExpr *DRE = dyn_cast<clang::DeclRefExpr>(expr)) {
        clang::ValueDecl *varDecl = DRE->getDecl();

        std::string varName = varDecl->getNameAsString();

        if (std::none_of(bitVariables.begin(), bitVariables.end(), [&varName](const BitVariable &item) { return item.name == varName; })) {
            clang::SourceManager &SM = TheRewriter.getSourceMgr();
            unsigned int varDeclLine = SM.getSpellingLineNumber(varDecl->getLocation());

            clang::QualType varType = varDecl->getType();
            if (auto *BT = varType->getAs<clang::BuiltinType>()) {
                switch (BT->getKind()) {
                    case clang::BuiltinType::UChar:
                    case clang::BuiltinType::Char_U:
                        bitVariables.push_back({varName, varDeclLine, "8", "unsigned"});
                        break;
                    case clang::BuiltinType::SChar:
                    case clang::BuiltinType::Char_S:
                        bitVariables.push_back({varName, varDeclLine, "8", "signed"});
                        break;
                    case clang::BuiltinType::UShort:
                        bitVariables.push_back({varName, varDeclLine, "16", "unsigned"});
                        break;
                    case clang::BuiltinType::Short:
                        bitVariables.push_back({varName, varDeclLine, "16", "signed"});
                        break;
                    case clang::BuiltinType::UInt:
                        bitVariables.push_back({varName, varDeclLine, "32", "unsigned"});
                        break;
                    case clang::BuiltinType::Int:
                        bitVariables.push_back({varName, varDeclLine, "32", "signed"});
                        break;
                    case clang::BuiltinType::ULong:
                        bitVariables.push_back({varName, varDeclLine, "64", "unsigned"});
                        break;
                    case clang::BuiltinType::Long:
                        bitVariables.push_back({varName, varDeclLine, "64", "signed"});
                        break;
                    default:
                        break;
                }
            }
        }
    }

    else if (clang::BinaryOperator *BO = dyn_cast<clang::BinaryOperator>(expr)) {
        if (BO->isAssignmentOp()) {
            clang::Expr *leftExpr = BO->getLHS()->IgnoreParenImpCasts();

            if (clang::DeclRefExpr *DRE = dyn_cast<clang::DeclRefExpr>(leftExpr)) {
                clang::ValueDecl *varDecl = DRE->getDecl();

                std::string varName = varDecl->getNameAsString();

                clang::SourceManager &SM = TheRewriter.getSourceMgr();
                unsigned int varDeclLine = SM.getSpellingLineNumber(varDecl->getLocation());

                clang::QualType varType = varDecl->getType();
                if (auto *BT = varType->getAs<clang::BuiltinType>()) {
                    switch (BT->getKind()) {
                        case clang::BuiltinType::UChar:
                        case clang::BuiltinType::Char_U:
                            bitVariables.push_back({varName, varDeclLine, "8", "unsigned"});
                            break;
                        case clang::BuiltinType::SChar:
                        case clang::BuiltinType::Char_S:
                            bitVariables.push_back({varName, varDeclLine, "8", "signed"});
                            break;
                        case clang::BuiltinType::UShort:
                            bitVariables.push_back({varName, varDeclLine, "16", "unsigned"});
                            break;
                        case clang::BuiltinType::Short:
                            bitVariables.push_back({varName, varDeclLine, "16", "signed"});
                            break;
                        case clang::BuiltinType::UInt:
                            bitVariables.push_back({varName, varDeclLine, "32", "unsigned"});
                            break;
                        case clang::BuiltinType::Int:
                            bitVariables.push_back({varName, varDeclLine, "32", "signed"});
                            break;
                        case clang::BuiltinType::ULong:
                            bitVariables.push_back({varName, varDeclLine, "64", "unsigned"});
                            break;
                        case clang::BuiltinType::Long:
                            bitVariables.push_back({varName, varDeclLine, "64", "signed"});
                            break;
                        default:
                            break;
                    }
                }
            }
        }
    }
}