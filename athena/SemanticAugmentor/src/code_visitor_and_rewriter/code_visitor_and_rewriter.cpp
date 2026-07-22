#include "../../include/code_visitor_and_rewriter/code_visitor_and_rewriter.h"

bool CodeVisitorAndRewriter::VisitFieldDecl(clang::FieldDecl *FD) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(FD->getBeginLoc())) {
        std::string fieldName = FD->getNameAsString();
        if (std::find(data.structureFields.begin(), data.structureFields.end(), fieldName) == data.structureFields.end()) {
            //Change Type
            std::string textToReplace = "long long " + fieldName;
            TheRewriter.ReplaceText(FD->getSourceRange(), textToReplace);
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitFunctionDecl(clang::FunctionDecl *FD) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(FD->getBeginLoc())) {
        currentFunction = FD->getNameAsString();

        if (currentFunction != "__VERIFIER_nondet_String" && currentFunction.find("__VERIFIER_nondet_") != std::string::npos) {
            //Change Type
            //std::string textToReplace = "__VERIFIER_nondet_longlong";
            //TheRewriter.ReplaceText(FD->getNameInfo().getSourceRange(), textToReplace);
        }

        if (currentFunction != "main" && !FD->getReturnType()->isVoidType() && std::find(data.functions.begin(), data.functions.end(), currentFunction) == data.functions.end()) {
            //Change Type
            std::string textToReplace = "long long";
            TheRewriter.ReplaceText(FD->getReturnTypeSourceRange(), textToReplace);
        }

        for (clang::ParmVarDecl *param : FD->parameters()) {
            std::string paramName = param->getNameAsString();
            auto it = std::find_if(data.functionParameters.begin(), data.functionParameters.end(), [&](const FunctionParameter& item) { return item.functionName == currentFunction && item.parameterName == paramName; });
            if (it == data.functionParameters.end()) {
                //Change Type
                std::string textToReplace = "long long " + paramName;
                TheRewriter.ReplaceText(param->getSourceRange(), textToReplace);
            }
        }

        if (FD->hasBody() && isFirstFunction) {
            //Instrument Wrap_Around Function
            std::string textToInsert = "long long wrap_around(long long value, long long lower_bound, long long upper_bound) {\n"
                                       "    long long range = upper_bound - lower_bound + 1;\n"
                                       "    if (value > upper_bound) {\n"
                                       "        return lower_bound + (value - upper_bound - 1) % range;\n"
                                       "    }\n"
                                       "    else if (value < lower_bound) {\n"
                                       "        return upper_bound - (lower_bound - value - 1) % range;\n"
                                       "    }\n"
                                       "    return value;\n"
                                       "}\n";
            TheRewriter.InsertTextBefore(FD->getBeginLoc(), textToInsert);
            isFirstFunction = false;
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitVarDecl(clang::VarDecl *VD) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(VD->getBeginLoc())) {
        clang::QualType varType = VD->getType();

        if (varType->isStructureType() || (varType->isArrayType() && varType->getAsArrayTypeUnsafe()->getElementType()->isStructureType())) {
            return true;
        }

        unsigned lineNumber = SM.getSpellingLineNumber(VD->getBeginLoc());
        if (modifiedLines.find(lineNumber) != modifiedLines.end()) {
            return true;
        }

        if (VD->hasGlobalStorage() && !VD->isStaticLocal()) {
            if (VD->hasInit()) {
                std::string varName = VD->getNameAsString();
                if (std::find(data.globalVariables.begin(), data.globalVariables.end(), varName) == data.globalVariables.end()) {
                    //Change Type
                    std::string textToReplace1 = "long long " + varName;
                    clang::SourceLocation startLoc = VD->getBeginLoc();
                    clang::SourceLocation endLoc = VD->getLocation();
                    TheRewriter.ReplaceText(clang::SourceRange(startLoc, endLoc), textToReplace1);
                    modifiedLines.insert(lineNumber);

                    //Inject Semantic
                    bool flag = false;
                    clang::Expr *initExpr = VD->getInit()->IgnoreParenImpCasts();
                    if (clang::DeclRefExpr *declRefExpr = clang::dyn_cast<clang::DeclRefExpr>(initExpr)) {
                        if (clang::VarDecl *varDecl = clang::dyn_cast<clang::VarDecl>(declRefExpr->getDecl())) {
                            if (varDecl->getType().getAsString() != varType.getAsString()) {
                                //Variable with Different Data Type
                                flag = true;
                            }
                        }
                    }
                    else if (clang::UnaryOperator *unaryOp = clang::dyn_cast<clang::UnaryOperator>(initExpr)) {
                        clang::UnaryOperatorKind unaryOpKind = unaryOp->getOpcode();
                        if (unaryOpKind == clang::UO_Minus) {
                            if (!clang::isa<clang::IntegerLiteral>(unaryOp->getSubExpr()->IgnoreImpCasts())) {
                                //-E
                                flag = true;
                            }
                        }
                    }
                    else if (clang::BinaryOperator *binaryOp = clang::dyn_cast<clang::BinaryOperator>(initExpr)) {
                        clang::BinaryOperatorKind binaryOpKind = binaryOp->getOpcode();
                        if (binaryOpKind == clang::BO_Add || binaryOpKind == clang::BO_Sub || binaryOpKind == clang::BO_Mul || binaryOpKind == clang::BO_Div || binaryOpKind == clang::BO_Rem) {
                            //E1 op E2 where op ∈ {+, -, *, /, %}
                            flag = true;
                        }
                    }
                    else if (clang::CallExpr *callExpr = clang::dyn_cast<clang::CallExpr>(initExpr)) {
                        if (clang::FunctionDecl *functionDecl = callExpr->getDirectCallee()) {
                            if (functionDecl->getReturnType().getAsString() != varType.getAsString()) {
                                //Function Call with Different Return Type
                                flag = true;
                            }
                        }
                    }
                    if (flag) {
                        clang::SourceRange initExprRange = initExpr->getSourceRange();
                        std::string initExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(initExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                        std::string bounds;
                        std::string varTypeStr = varType.getAsString();
                        if (varTypeStr.find("const ") == 0) {
                            varTypeStr.erase(0, 6);
                        }
                        if (varTypeStr == "unsigned char") {
                            bounds = "0, UCHAR_MAX";
                        } else if (varTypeStr == "char") {
                            bounds = "SCHAR_MIN, SCHAR_MAX";
                        } else if (varTypeStr == "unsigned short") {
                            bounds = "0, USHRT_MAX";
                        } else if (varTypeStr == "short") {
                            bounds = "SHRT_MIN, SHRT_MAX";
                        } else if (varTypeStr == "unsigned int") {
                            bounds = "0, UINT_MAX";
                        } else if (varTypeStr == "int") {
                            bounds = "INT_MIN, INT_MAX";
                        } else if (varTypeStr == "unsigned long") {
                            bounds = "0, ULONG_MAX";
                        } else if (varTypeStr == "long") {
                            bounds = "LONG_MIN, LONG_MAX";
                        } else if (varTypeStr == "<dependent type>") {
                            bounds = "0, SIZE_MAX";
                        }

                        std::string textToReplace2 = "wrap_around(" + initExprStr + ", " + bounds + ")";
                        TheRewriter.ReplaceText(initExprRange, textToReplace2);
                    }
                }
            }

            else {
                std::string varName = VD->getNameAsString();
                if (std::find(data.globalVariables.begin(), data.globalVariables.end(), varName) == data.globalVariables.end()) {
                    //Change Type
                    std::string textToReplace = "long long " + varName;
                    clang::SourceLocation startLoc = VD->getBeginLoc();
                    clang::SourceLocation endLoc = VD->getLocation();
                    TheRewriter.ReplaceText(clang::SourceRange(startLoc, endLoc), textToReplace);
                    modifiedLines.insert(lineNumber);
                }
            }
        }

        else if (VD->isLocalVarDecl()) {
            if (VD->hasInit()) {
                std::string varName = VD->getNameAsString();
                auto it = std::find_if(data.localVariables.begin(), data.localVariables.end(), [&](const LocalVariable& item) { return item.functionName == currentFunction && item.variableName == varName; });
                if (it == data.localVariables.end()) {
                    //Change Type
                    std::string textToReplace1 = "long long " + varName;
                    clang::SourceLocation startLoc = VD->getBeginLoc();
                    clang::SourceLocation endLoc = VD->getLocation();
                    TheRewriter.ReplaceText(clang::SourceRange(startLoc, endLoc), textToReplace1);
                    modifiedLines.insert(lineNumber);

                    //Inject Semantic
                    bool flag = false;
                    clang::Expr *initExpr = VD->getInit()->IgnoreParenImpCasts();
                    if (clang::DeclRefExpr *declRefExpr = clang::dyn_cast<clang::DeclRefExpr>(initExpr)) {
                        if (clang::VarDecl *varDecl = clang::dyn_cast<clang::VarDecl>(declRefExpr->getDecl())) {
                            if (varDecl->getType().getAsString() != varType.getAsString()) {
                                //Variable with Different Data Type
                                flag = true;
                            }
                        }
                    }
                    else if (clang::UnaryOperator *unaryOp = clang::dyn_cast<clang::UnaryOperator>(initExpr)) {
                        clang::UnaryOperatorKind unaryOpKind = unaryOp->getOpcode();
                        if (unaryOpKind == clang::UO_Minus) {
                            if (!clang::isa<clang::IntegerLiteral>(unaryOp->getSubExpr()->IgnoreImpCasts())) {
                                //-E
                                flag = true;
                            }
                        }
                    }
                    else if (clang::BinaryOperator *binaryOp = clang::dyn_cast<clang::BinaryOperator>(initExpr)) {
                        clang::BinaryOperatorKind binaryOpKind = binaryOp->getOpcode();
                        if (binaryOpKind == clang::BO_Add || binaryOpKind == clang::BO_Sub || binaryOpKind == clang::BO_Mul || binaryOpKind == clang::BO_Div || binaryOpKind == clang::BO_Rem) {
                            //E1 op E2 where op ∈ {+, -, *, /, %}
                            flag = true;
                        }
                    }
                    else if (clang::CallExpr *callExpr = clang::dyn_cast<clang::CallExpr>(initExpr)) {
                        if (clang::FunctionDecl *functionDecl = callExpr->getDirectCallee()) {
                            if (functionDecl->getReturnType().getAsString() != varType.getAsString()) {
                                //Function Call with Different Return Type
                                flag = true;
                            }
                        }
                    }
                    if (flag) {
                        clang::SourceRange initExprRange = initExpr->getSourceRange();
                        std::string initExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(initExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                        std::string bounds;
                        std::string varTypeStr = varType.getAsString();
                        if (varTypeStr.find("const ") == 0) {
                            varTypeStr.erase(0, 6);
                        }
                        if (varTypeStr == "unsigned char") {
                            bounds = "0, UCHAR_MAX";
                        } else if (varTypeStr == "char") {
                            bounds = "SCHAR_MIN, SCHAR_MAX";
                        } else if (varTypeStr == "unsigned short") {
                            bounds = "0, USHRT_MAX";
                        } else if (varTypeStr == "short") {
                            bounds = "SHRT_MIN, SHRT_MAX";
                        } else if (varTypeStr == "unsigned int") {
                            bounds = "0, UINT_MAX";
                        } else if (varTypeStr == "int") {
                            bounds = "INT_MIN, INT_MAX";
                        } else if (varTypeStr == "unsigned long") {
                            bounds = "0, ULONG_MAX";
                        } else if (varTypeStr == "long") {
                            bounds = "LONG_MIN, LONG_MAX";
                        } else if (varTypeStr == "<dependent type>") {
                            bounds = "0, SIZE_MAX";
                        }

                        std::string textToReplace2 = "wrap_around(" + initExprStr + ", " + bounds + ")";
                        TheRewriter.ReplaceText(initExprRange, textToReplace2);
                    }
                }
            }

            else {
                std::string varName = VD->getNameAsString();
                auto it = std::find_if(data.localVariables.begin(), data.localVariables.end(), [&](const LocalVariable& item) { return item.functionName == currentFunction && item.variableName == varName; });
                if (it == data.localVariables.end()) {
                    //Change Type
                    std::string textToReplace = "long long " + varName;
                    clang::SourceLocation startLoc = VD->getBeginLoc();
                    clang::SourceLocation endLoc = VD->getLocation();
                    TheRewriter.ReplaceText(clang::SourceRange(startLoc, endLoc), textToReplace);
                    modifiedLines.insert(lineNumber);
                }
            }
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitCallExpr(clang::CallExpr *CE) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(CE->getBeginLoc())) {
        if (clang::FunctionDecl *FD = CE->getDirectCallee()) {
            /*
            std::string funcName = FD->getNameInfo().getName().getAsString();
            if (funcName != "__VERIFIER_nondet_String" && funcName.find("__VERIFIER_nondet_") != std::string::npos) {
                //__VERIFIER_nondet_T()
                //Inject Semantic
                std::string bounds;
                std::string funcType = CE->getType().getAsString();
                if (funcType.find("const ") == 0) {
                    funcType.erase(0, 6);
                }
                if (funcType == "unsigned char") {
                    bounds = "0, UCHAR_MAX";
                } else if (funcType == "char") {
                    bounds = "SCHAR_MIN, SCHAR_MAX";
                } else if (funcType == "unsigned short") {
                    bounds = "0, USHRT_MAX";
                } else if (funcType == "short") {
                    bounds = "SHRT_MIN, SHRT_MAX";
                } else if (funcType == "unsigned int") {
                    bounds = "0, UINT_MAX";
                } else if (funcType == "int") {
                    bounds = "INT_MIN, INT_MAX";
                } else if (funcType == "unsigned long") {
                    bounds = "0, ULONG_MAX";
                } else if (funcType == "long") {
                    bounds = "LONG_MIN, LONG_MAX";
                } else if (funcType == "<dependent type>") {
                    bounds = "0, SIZE_MAX";
                }

                std::string textToReplace = "wrap_around(__VERIFIER_nondet_longlong(), " + bounds + ")";
                TheRewriter.ReplaceText(CE->getSourceRange(), textToReplace);
            }
            */
        }

        for (clang::Expr *argExpr : CE->arguments()) {
            //Inject Semantic
            bool flag = false;
            argExpr = argExpr->IgnoreParenImpCasts();
            if (clang::UnaryOperator *unaryOp = clang::dyn_cast<clang::UnaryOperator>(argExpr)) {
                clang::UnaryOperatorKind unaryOpKind = unaryOp->getOpcode();
                if (unaryOpKind == clang::UO_Minus) {
                    if (!clang::isa<clang::IntegerLiteral>(unaryOp->getSubExpr()->IgnoreImpCasts())) {
                        //-E
                        flag = true;
                    }
                }
            }
            else if (clang::BinaryOperator *binaryOp = clang::dyn_cast<clang::BinaryOperator>(argExpr)) {
                clang::BinaryOperatorKind binaryOpKind = binaryOp->getOpcode();
                if (binaryOpKind == clang::BO_Add || binaryOpKind == clang::BO_Sub || binaryOpKind == clang::BO_Mul || binaryOpKind == clang::BO_Div || binaryOpKind == clang::BO_Rem) {
                    //E1 op E2 where op ∈ {+, -, *, /, %}
                    flag = true;
                }
            }
            if (flag) {
                if (!HasMatchingData(argExpr)) {
                    clang::SourceRange argExprRange = argExpr->getSourceRange();
                    std::string argExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(argExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                    std::string bounds;
                    std::string argExprType = argExpr->getType().getAsString();
                    if (argExprType.find("const ") == 0) {
                        argExprType.erase(0, 6);
                    }
                    if (argExprType == "unsigned char") {
                        bounds = "0, UCHAR_MAX";
                    } else if (argExprType == "char") {
                        bounds = "SCHAR_MIN, SCHAR_MAX";
                    } else if (argExprType == "unsigned short") {
                        bounds = "0, USHRT_MAX";
                    } else if (argExprType == "short") {
                        bounds = "SHRT_MIN, SHRT_MAX";
                    } else if (argExprType == "unsigned int") {
                        bounds = "0, UINT_MAX";
                    } else if (argExprType == "int") {
                        bounds = "INT_MIN, INT_MAX";
                    } else if (argExprType == "unsigned long") {
                        bounds = "0, ULONG_MAX";
                    } else if (argExprType == "long") {
                        bounds = "LONG_MIN, LONG_MAX";
                    } else if (argExprType == "<dependent type>") {
                        bounds = "0, SIZE_MAX";
                    }

                    std::string textToReplace = "wrap_around(" + argExprStr + ", " + bounds + ")";
                    TheRewriter.ReplaceText(argExprRange, textToReplace);
                }
            }
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitUnaryOperator(clang::UnaryOperator *UO) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(UO->getBeginLoc())) {
        if (UO->isIncrementDecrementOp()) {
            clang::SourceLocation lineStartLoc = SM.translateLineCol(SM.getFileID(UO->getBeginLoc()), SM.getSpellingLineNumber(UO->getBeginLoc()), 1);
            clang::SourceLocation lineEndLoc = lineStartLoc;
            while (SM.getCharacterData(lineEndLoc)[0] != '\n' && SM.getCharacterData(lineEndLoc)[0] != '\0') {
                lineEndLoc = lineEndLoc.getLocWithOffset(1);
            }
            std::string lineText = std::string(SM.getCharacterData(lineStartLoc), SM.getCharacterData(lineEndLoc) - SM.getCharacterData(lineStartLoc));

            bool flag = false;
            std::string pattern = "^\\s*(if|else\\s+if|while|\\}\\s+while)\\b";
            std::regex keywordRegex(pattern);
            if (std::regex_search(lineText, keywordRegex)) {
                flag = true;
            }

            if (flag && (UO->getOpcode() == clang::UO_PostDec || UO->getOpcode() == clang::UO_PostInc)) {
                //V-- or V++ in IF, ELSE IF, WHILE, or DO WHILE
                //HandleCondition2
            }

            else {
                clang::Expr *subExpr = UO->getSubExpr()->IgnoreParenImpCasts();
                if (!HasMatchingData(subExpr)) {
                    //--V or ++V in IF, ELSE IF, WHILE, or DO WHILE
                    //--V, ++V, V--, or V++
                    //Inject Semantic
                    clang::SourceRange subExprRange = subExpr->getSourceRange();
                    std::string subExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(subExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                    std::string bounds;
                    std::string subExprType = subExpr->getType().getAsString();
                    if (subExprType.find("const ") == 0) {
                        subExprType.erase(0, 6);
                    }
                    if (subExprType == "unsigned char") {
                        bounds = "0, UCHAR_MAX";
                    } else if (subExprType == "char") {
                        bounds = "SCHAR_MIN, SCHAR_MAX";
                    } else if (subExprType == "unsigned short") {
                        bounds = "0, USHRT_MAX";
                    } else if (subExprType == "short") {
                        bounds = "SHRT_MIN, SHRT_MAX";
                    } else if (subExprType == "unsigned int") {
                        bounds = "0, UINT_MAX";
                    } else if (subExprType == "int") {
                        bounds = "INT_MIN, INT_MAX";
                    } else if (subExprType == "unsigned long") {
                        bounds = "0, ULONG_MAX";
                    } else if (subExprType == "long") {
                        bounds = "LONG_MIN, LONG_MAX";
                    } else if (subExprType == "<dependent type>") {
                        bounds = "0, SIZE_MAX";
                    }

                    std::string op;
                    switch (UO->getOpcode()) {
                        case clang::UO_PreDec:
                        case clang::UO_PostDec:
                            op = "-";
                            break;
                        case clang::UO_PreInc:
                        case clang::UO_PostInc:
                            op = "+";
                            break;
                        default:
                            break;
                    }

                    std::string textToReplace = "(" + subExprStr + " = wrap_around(" + subExprStr + " " + op + " 1, " + bounds + "))";
                    TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
                }
            }
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitBinaryOperator(clang::BinaryOperator *BO) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(BO->getBeginLoc())) {
        if (BO->isAssignmentOp()) {
            if (BO->getOpcode() == clang::BO_Assign) {
                //Inject Semantic
                bool flag = false;
                clang::Expr *leftExpr = BO->getLHS()->IgnoreParenImpCasts();
                clang::Expr *rightExpr = BO->getRHS()->IgnoreParenImpCasts();
                if (clang::DeclRefExpr *declRefExpr = clang::dyn_cast<clang::DeclRefExpr>(rightExpr)) {
                    if (clang::VarDecl *varDecl = clang::dyn_cast<clang::VarDecl>(declRefExpr->getDecl())) {
                        if (varDecl->getType().getAsString() != leftExpr->getType().getAsString()) {
                            //Variable with Different Data Type
                            flag = true;
                        }
                    }
                }
                else if (clang::UnaryOperator *unaryOp = clang::dyn_cast<clang::UnaryOperator>(rightExpr)) {
                    clang::UnaryOperatorKind unaryOpKind = unaryOp->getOpcode();
                    if (unaryOpKind == clang::UO_Minus) {
                        if (!clang::isa<clang::IntegerLiteral>(unaryOp->getSubExpr()->IgnoreImpCasts())) {
                            //V = -E;
                            flag = true;
                        }
                    }
                }
                else if (clang::BinaryOperator *binaryOp = clang::dyn_cast<clang::BinaryOperator>(rightExpr)) {
                    clang::BinaryOperatorKind binaryOpKind = binaryOp->getOpcode();
                    if (binaryOpKind == clang::BO_Add || binaryOpKind == clang::BO_Sub || binaryOpKind == clang::BO_Mul || binaryOpKind == clang::BO_Div || binaryOpKind == clang::BO_Rem) {
                        //V = E1 op E2; where op ∈ {+, -, *, /, %}
                        flag = true;
                    }
                }
                else if (clang::CallExpr *callExpr = clang::dyn_cast<clang::CallExpr>(rightExpr)) {
                    if (clang::FunctionDecl *functionDecl = callExpr->getDirectCallee()) {
                        if (functionDecl->getReturnType().getAsString() != leftExpr->getType().getAsString()) {
                            //Function Call with Different Return Type
                            flag = true;
                        }
                    }
                }
                if (flag) {
                    if (!HasMatchingData(leftExpr)) {
                        clang::SourceRange rightExprRange = rightExpr->getSourceRange();
                        std::string rightExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(rightExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                        std::string bounds;
                        std::string leftExprType = leftExpr->getType().getAsString();
                        if (leftExprType.find("const ") == 0) {
                            leftExprType.erase(0, 6);
                        }
                        if (leftExprType == "unsigned char") {
                            bounds = "0, UCHAR_MAX";
                        } else if (leftExprType == "char") {
                            bounds = "SCHAR_MIN, SCHAR_MAX";
                        } else if (leftExprType == "unsigned short") {
                            bounds = "0, USHRT_MAX";
                        } else if (leftExprType == "short") {
                            bounds = "SHRT_MIN, SHRT_MAX";
                        } else if (leftExprType == "unsigned int") {
                            bounds = "0, UINT_MAX";
                        } else if (leftExprType == "int") {
                            bounds = "INT_MIN, INT_MAX";
                        } else if (leftExprType == "unsigned long") {
                            bounds = "0, ULONG_MAX";
                        } else if (leftExprType == "long") {
                            bounds = "LONG_MIN, LONG_MAX";
                        } else if (leftExprType == "<dependent type>") {
                            bounds = "0, SIZE_MAX";
                        }

                        std::string textToReplace2 = "wrap_around(" + rightExprStr + ", " + bounds + ")";
                        TheRewriter.ReplaceText(rightExprRange, textToReplace2);
                    }
                }
            }

            else {
                clang::BinaryOperatorKind opKind = BO->getOpcode();

                if (opKind == clang::BO_AddAssign || opKind == clang::BO_SubAssign || opKind == clang::BO_MulAssign || opKind == clang::BO_DivAssign || opKind == clang::BO_RemAssign) {
                    //V op= E; where op ∈ {+, -, *, /, %}
                    //Inject Semantic
                    clang::Expr *leftExpr = BO->getLHS()->IgnoreParenImpCasts();
                    if (!HasMatchingData(leftExpr)) {
                        clang::SourceRange leftExprRange = leftExpr->getSourceRange();
                        std::string leftExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(leftExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                        clang::Expr *rightExpr = BO->getRHS()->IgnoreParenImpCasts();
                        clang::SourceRange rightExprRange = rightExpr->getSourceRange();
                        std::string rightExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(rightExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                        std::string bounds;
                        std::string leftExprType = leftExpr->getType().getAsString();
                        if (leftExprType.find("const ") == 0) {
                            leftExprType.erase(0, 6);
                        }
                        if (leftExprType == "unsigned char") {
                            bounds = "0, UCHAR_MAX";
                        } else if (leftExprType == "char") {
                            bounds = "SCHAR_MIN, SCHAR_MAX";
                        } else if (leftExprType == "unsigned short") {
                            bounds = "0, USHRT_MAX";
                        } else if (leftExprType == "short") {
                            bounds = "SHRT_MIN, SHRT_MAX";
                        } else if (leftExprType == "unsigned int") {
                            bounds = "0, UINT_MAX";
                        } else if (leftExprType == "int") {
                            bounds = "INT_MIN, INT_MAX";
                        } else if (leftExprType == "unsigned long") {
                            bounds = "0, ULONG_MAX";
                        } else if (leftExprType == "long") {
                            bounds = "LONG_MIN, LONG_MAX";
                        } else if (leftExprType == "<dependent type>") {
                            bounds = "0, SIZE_MAX";
                        }

                        std::string op;
                        switch (opKind) {
                            case clang::BO_AddAssign:
                                op = "+";
                                break;
                            case clang::BO_SubAssign:
                                op = "-";
                                break;
                            case clang::BO_MulAssign:
                                op = "*";
                                break;
                            case clang::BO_DivAssign:
                                op = "/";
                                break;
                            case clang::BO_RemAssign:
                                op = "%";
                                break;
                            default:
                                break;
                        }

                        std::string textToInsert = leftExprStr + " = wrap_around(" + leftExprStr + " " + op + " (" + rightExprStr + "), " + bounds + ")";
                        TheRewriter.ReplaceText(BO->getSourceRange(), textToInsert);
                    }
                }
            }
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitIfStmt(clang::IfStmt *IS) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(IS->getBeginLoc())) {
        HandleCondition1(IS->getCond());
        HandleCondition2(IS->getCond(), IS->getThen()->getBeginLoc(), IS->getThen()->getEndLoc());
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitForStmt(clang::ForStmt *FS) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(FS->getBeginLoc())) {
        clang::Expr *condExpr = FS->getCond();
        if (condExpr) {
            HandleCondition1(condExpr);
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitWhileStmt(clang::WhileStmt *WS) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(WS->getBeginLoc())) {
        HandleCondition1(WS->getCond());
        HandleCondition2(WS->getCond(), WS->getBody()->getBeginLoc(), WS->getBody()->getEndLoc());
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitDoStmt(clang::DoStmt *DS) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(DS->getBeginLoc())) {
        HandleCondition1(DS->getCond());
        HandleCondition2(DS->getCond(), DS->getBody()->getBeginLoc(), DS->getRParenLoc().getLocWithOffset(1));
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitReturnStmt(clang::ReturnStmt *RS) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(RS->getBeginLoc())) {
        //Inject Semantic
        bool flag = false;
        clang::Expr *retExpr = RS->getRetValue();
        if (retExpr) {
            retExpr = retExpr->IgnoreParenImpCasts();
            if (clang::UnaryOperator *unaryOp = clang::dyn_cast<clang::UnaryOperator>(retExpr)) {
                clang::UnaryOperatorKind unaryOpKind = unaryOp->getOpcode();
                if (unaryOpKind == clang::UO_Minus) {
                    if (!clang::isa<clang::IntegerLiteral>(unaryOp->getSubExpr()->IgnoreImpCasts())) {
                        //-E
                        flag = true;
                    }
                }
            } else if (clang::BinaryOperator *binaryOp = clang::dyn_cast<clang::BinaryOperator>(retExpr)) {
                clang::BinaryOperatorKind binaryOpKind = binaryOp->getOpcode();
                if (binaryOpKind == clang::BO_Add || binaryOpKind == clang::BO_Sub || binaryOpKind == clang::BO_Mul ||
                    binaryOpKind == clang::BO_Div || binaryOpKind == clang::BO_Rem) {
                    //E1 op E2 where op ∈ {+, -, *, /, %}
                    flag = true;
                }
            }
            if (flag) {
                if (!HasMatchingData(retExpr)) {
                    clang::SourceRange retExprRange = retExpr->getSourceRange();
                    std::string retExprStr = clang::Lexer::getSourceText(
                            clang::CharSourceRange::getTokenRange(retExprRange), TheRewriter.getSourceMgr(),
                            TheRewriter.getLangOpts()).str();

                    std::string bounds;
                    std::string retExprType = retExpr->getType().getAsString();
                    if (retExprType.find("const ") == 0) {
                        retExprType.erase(0, 6);
                    }
                    if (retExprType == "unsigned char") {
                        bounds = "0, UCHAR_MAX";
                    } else if (retExprType == "char") {
                        bounds = "SCHAR_MIN, SCHAR_MAX";
                    } else if (retExprType == "unsigned short") {
                        bounds = "0, USHRT_MAX";
                    } else if (retExprType == "short") {
                        bounds = "SHRT_MIN, SHRT_MAX";
                    } else if (retExprType == "unsigned int") {
                        bounds = "0, UINT_MAX";
                    } else if (retExprType == "int") {
                        bounds = "INT_MIN, INT_MAX";
                    } else if (retExprType == "unsigned long") {
                        bounds = "0, ULONG_MAX";
                    } else if (retExprType == "long") {
                        bounds = "LONG_MIN, LONG_MAX";
                    } else if (retExprType == "<dependent type>") {
                        bounds = "0, SIZE_MAX";
                    }

                    std::string textToReplace = "wrap_around(" + retExprStr + ", " + bounds + ")";
                    TheRewriter.ReplaceText(retExprRange, textToReplace);
                }
            }
        }
    }
    return true;
}

void CodeVisitorAndRewriter::HandleCondition1(clang::Expr *expr) {
    expr = expr->IgnoreParenImpCasts();

    if (auto *unaryOp = clang::dyn_cast<clang::UnaryOperator>(expr)) {
        if (unaryOp->getOpcode() == clang::UO_LNot) {
            //!E
            //Get Sub-Expression(s)
            HandleCondition1(unaryOp->getSubExpr());
        }

        else if (unaryOp->getOpcode() == clang::UO_Minus) {
            if (!clang::isa<clang::IntegerLiteral>(unaryOp->getSubExpr()->IgnoreImpCasts())) {
                if (!HasMatchingData(expr)) {
                    //-E
                    //Inject Semantic
                    clang::SourceRange exprRange = expr->getSourceRange();
                    std::string exprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(exprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                    std::string bounds;
                    std::string exprType = expr->getType().getAsString();
                    if (exprType.find("const ") == 0) {
                        exprType.erase(0, 6);
                    }
                    if (exprType == "unsigned char") {
                        bounds = "0, UCHAR_MAX";
                    } else if (exprType == "char") {
                        bounds = "SCHAR_MIN, SCHAR_MAX";
                    } else if (exprType == "unsigned short") {
                        bounds = "0, USHRT_MAX";
                    } else if (exprType == "short") {
                        bounds = "SHRT_MIN, SHRT_MAX";
                    } else if (exprType == "unsigned int") {
                        bounds = "0, UINT_MAX";
                    } else if (exprType == "int") {
                        bounds = "INT_MIN, INT_MAX";
                    } else if (exprType == "unsigned long") {
                        bounds = "0, ULONG_MAX";
                    } else if (exprType == "long") {
                        bounds = "LONG_MIN, LONG_MAX";
                    } else if (exprType == "<dependent type>") {
                        bounds = "0, SIZE_MAX";
                    }

                    std::string textToReplace = "wrap_around(" + exprStr + ", " + bounds + ")";
                    TheRewriter.ReplaceText(expr->getSourceRange(), textToReplace);
                }
            }
        }
    }

    if (auto *binaryOp = clang::dyn_cast<clang::BinaryOperator>(expr)) {
        if (binaryOp->isLogicalOp() || binaryOp->isComparisonOp()) {
            //E1 op E2, where op ∈ {&&, ||, ==, !=, <, <=, >, >=}
            //Get Sub-Expression(s)
            HandleCondition1(binaryOp->getLHS());
            HandleCondition1(binaryOp->getRHS());
        }

        else if (binaryOp->getOpcode() == clang::BO_Add || binaryOp->getOpcode() == clang::BO_Sub || binaryOp->getOpcode() == clang::BO_Mul || binaryOp->getOpcode() == clang::BO_Div || binaryOp->getOpcode() == clang::BO_Rem) {
            if (!HasMatchingData(expr)) {
                //E1 op E2, where op {+, -, *, /, %}
                //Inject Semantic
                clang::SourceRange exprRange = expr->getSourceRange();
                std::string exprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(exprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                std::string bounds;
                std::string exprType = expr->getType().getAsString();
                if (exprType.find("const ") == 0) {
                    exprType.erase(0, 6);
                }
                if (exprType == "unsigned char") {
                    bounds = "0, UCHAR_MAX";
                } else if (exprType == "char") {
                    bounds = "SCHAR_MIN, SCHAR_MAX";
                } else if (exprType == "unsigned short") {
                    bounds = "0, USHRT_MAX";
                } else if (exprType == "short") {
                    bounds = "SHRT_MIN, SHRT_MAX";
                } else if (exprType == "unsigned int") {
                    bounds = "0, UINT_MAX";
                } else if (exprType == "int") {
                    bounds = "INT_MIN, INT_MAX";
                } else if (exprType == "unsigned long") {
                    bounds = "0, ULONG_MAX";
                } else if (exprType == "long") {
                    bounds = "LONG_MIN, LONG_MAX";
                } else if (exprType == "<dependent type>") {
                    bounds = "0, SIZE_MAX";
                }

                std::string textToReplace = "wrap_around(" + exprStr + ", " + bounds + ")";
                TheRewriter.ReplaceText(expr->getSourceRange(), textToReplace);
            }
        }
    }
}

void CodeVisitorAndRewriter::HandleCondition2(clang::Expr *expr, clang::SourceLocation startLoc, clang::SourceLocation endLoc) {
    expr = expr->IgnoreParenImpCasts();

    if (auto *unaryOp = clang::dyn_cast<clang::UnaryOperator>(expr)) {
        if (unaryOp->getOpcode() == clang::UO_PostDec || unaryOp->getOpcode() == clang::UO_PostInc) {
            clang::Expr *subExpr = unaryOp->getSubExpr()->IgnoreParenImpCasts();
            if (!HasMatchingData(subExpr)) {
                //V-- or V++ in IF, ELSE IF, WHILE, or DO WHILE
                //Inject Semantic
                clang::SourceRange subExprRange = subExpr->getSourceRange();
                std::string subExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(subExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                std::string bounds;
                std::string subExprType = subExpr->getType().getAsString();
                if (subExprType.find("const ") == 0) {
                    subExprType.erase(0, 6);
                }
                if (subExprType == "unsigned char") {
                    bounds = "0, UCHAR_MAX";
                } else if (subExprType == "char") {
                    bounds = "SCHAR_MIN, SCHAR_MAX";
                } else if (subExprType == "unsigned short") {
                    bounds = "0, USHRT_MAX";
                } else if (subExprType == "short") {
                    bounds = "SHRT_MIN, SHRT_MAX";
                } else if (subExprType == "unsigned int") {
                    bounds = "0, UINT_MAX";
                } else if (subExprType == "int") {
                    bounds = "INT_MIN, INT_MAX";
                } else if (subExprType == "unsigned long") {
                    bounds = "0, ULONG_MAX";
                } else if (subExprType == "long") {
                    bounds = "LONG_MIN, LONG_MAX";
                } else if (subExprType == "<dependent type>") {
                    bounds = "0, SIZE_MAX";
                }

                std::string textToInsert = "\n" + subExprStr + " = wrap_around(" + subExprStr + ", " + bounds + ");";
                TheRewriter.InsertTextAfterToken(startLoc, textToInsert);
                TheRewriter.InsertTextAfterToken(endLoc, textToInsert);
            }
        }
    }

    if (auto *binaryOp = clang::dyn_cast<clang::BinaryOperator>(expr)) {
        //Other Cases
        //Get Sub-Expression(s)
        HandleCondition2(binaryOp->getLHS(), startLoc, endLoc);
        HandleCondition2(binaryOp->getRHS(), startLoc, endLoc);
    }
}

bool CodeVisitorAndRewriter::HasMatchingData(clang::Expr *expr) {
    expr = expr->IgnoreParenImpCasts();

    if (!expr) {
        return false;
    }

    if (auto *DRE = dyn_cast<clang::DeclRefExpr>(expr)) {
        std::string varName = DRE->getNameInfo().getAsString();
        if (std::find(data.macros.begin(), data.macros.end(), varName) != data.macros.end()) {
            return true;
        }
        auto it1 = std::find_if(data.functionParameters.begin(), data.functionParameters.end(), [&](const FunctionParameter& item) { return item.functionName == currentFunction && item.parameterName == varName; });
        if (it1 != data.functionParameters.end()) {
            return true;
        }
        if (std::find(data.globalVariables.begin(), data.globalVariables.end(), varName) != data.globalVariables.end()) {
            return true;
        }
        auto it2 = std::find_if(data.localVariables.begin(), data.localVariables.end(), [&](const LocalVariable& item) { return item.functionName == currentFunction && item.variableName == varName; });
        if (it2 != data.localVariables.end()) {
            return true;
        }
    }

    else if (auto *CE = dyn_cast<clang::CallExpr>(expr)) {
        if (auto *FD = CE->getDirectCallee()) {
            std::string funcName = FD->getNameInfo().getName().getAsString();
            if (std::find(data.functions.begin(), data.functions.end(), funcName) != data.functions.end()) {
                return true;
            }
        }
    }

    else if (auto *ASE = dyn_cast<clang::ArraySubscriptExpr>(expr)) {
        return false;
    }

    else if (auto *ME = dyn_cast<clang::MemberExpr>(expr)) {
        std::string memberName = ME->getMemberNameInfo().getAsString();
        if (std::find(data.structureFields.begin(), data.structureFields.end(), memberName) != data.structureFields.end()) {
            return true;
        }
    }

    for (auto *subStmt : expr->children()) {
        if (auto *subExpr = dyn_cast<clang::Expr>(subStmt)) {
            if (HasMatchingData(subExpr)) {
                return true;
            }
        }
    }

    return false;
}