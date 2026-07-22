#include "../../include/code_visitor_and_rewriter/tracking_rewriter.h"
#include "clang/Lex/Lexer.h"

void TrackingRewriter::markReplaced(clang::SourceRange range) {
    auto &SM = rewriter_.getSourceMgr();
    auto begin = SM.getFileOffset(SM.getExpansionLoc(range.getBegin()));
    auto end = SM.getFileOffset(clang::Lexer::getLocForEndOfToken(
        SM.getExpansionLoc(range.getEnd()), 0, SM, rewriter_.getLangOpts()));
    ranges_.push_back({begin, end});
}

void TrackingRewriter::markReplaced(clang::CharSourceRange range) {
    auto &SM = rewriter_.getSourceMgr();
    auto begin = SM.getFileOffset(SM.getExpansionLoc(range.getBegin()));
    auto end = SM.getFileOffset(SM.getExpansionLoc(range.getEnd()));
    if (range.isTokenRange()) {
        end = SM.getFileOffset(clang::Lexer::getLocForEndOfToken(
            SM.getExpansionLoc(range.getEnd()), 0, SM, rewriter_.getLangOpts()));
    }
    ranges_.push_back({begin, end});
}

bool TrackingRewriter::isReplaced(clang::SourceRange range) const {
    auto &SM = rewriter_.getSourceMgr();
    auto begin = SM.getFileOffset(SM.getExpansionLoc(range.getBegin()));
    auto end = SM.getFileOffset(clang::Lexer::getLocForEndOfToken(
        SM.getExpansionLoc(range.getEnd()), 0, SM, rewriter_.getLangOpts()));

    for (const auto &r : ranges_) {
        if (begin >= r.begin && end <= r.end) return true;
    }
    return false;
}

