#include "../../include/bit_operation_visitor/bit_operation_visitor.h"

bool BitOperationVisitor::VisitBinaryOperator(clang::BinaryOperator *BO) {
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
                    hasBitOperation = true;
                }
            }
        }
        else if (BO->isBitwiseOp() || BO->isShiftOp()) {
            //E1 op E2 where op ∈ {&, |, ^, <<, >>}
            hasBitOperation = true;
        }
    }
    return true;
}