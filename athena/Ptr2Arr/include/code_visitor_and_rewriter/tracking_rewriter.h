#ifndef TRACKING_REWRITER_H
#define TRACKING_REWRITER_H

#include "clang/Rewrite/Core/Rewriter.h"
#include <vector>

// Wraps clang::Rewriter and records which ranges have been replaced, so that a
// later pass does not rewrite the same text twice.
//
// NOTE on the return values.  Every method below faithfully returns what
// clang::Rewriter returns, and Clang's contract is that these return **true on
// failure** -- the location is inside a macro expansion, or otherwise not
// rewritable.  As of 2026-09-07 *none* of the 129 call sites across Ptr2Arr,
// SemanticAugmentor and TypeAnnotator inspects that value, so a rewrite that
// does not happen is indistinguishable from one that does: the emitted C is
// then the *original* text at that position, and everything downstream (the
// LTS translation and the termination analysis) reasons about a program that
// was never produced.  If you add a call, check the result.
class TrackingRewriter {
public:
    explicit TrackingRewriter(clang::Rewriter &rewriter) : rewriter_(rewriter) {}

    bool ReplaceText(clang::SourceRange range, llvm::StringRef str) {
        markReplaced(range);
        return rewriter_.ReplaceText(range, str);
    }

    bool ReplaceText(clang::CharSourceRange range, llvm::StringRef str) {
        markReplaced(range);
        return rewriter_.ReplaceText(range, str);
    }

    bool ReplaceText(clang::SourceLocation loc, unsigned len, llvm::StringRef str) {
        return rewriter_.ReplaceText(loc, len, str);
    }

    bool InsertText(clang::SourceLocation loc, llvm::StringRef str, bool after = true, bool indent = false) {
        return rewriter_.InsertText(loc, str, after, indent);
    }

    bool InsertTextBefore(clang::SourceLocation loc, llvm::StringRef str) {
        return rewriter_.InsertTextBefore(loc, str);
    }

    bool InsertTextAfterToken(clang::SourceLocation loc, llvm::StringRef str) {
        return rewriter_.InsertTextAfterToken(loc, str);
    }

    bool RemoveText(clang::SourceLocation loc, unsigned len) {
        return rewriter_.RemoveText(loc, len);
    }

    bool RemoveText(clang::SourceRange range) {
        return rewriter_.RemoveText(range);
    }

    bool RemoveText(clang::CharSourceRange range) {
        return rewriter_.RemoveText(range);
    }

    std::string getRewrittenText(clang::SourceRange range) const {
        return rewriter_.getRewrittenText(range);
    }

    std::string getRewrittenText(clang::CharSourceRange range) const {
        return rewriter_.getRewrittenText(range);
    }

    clang::SourceManager& getSourceMgr() { return rewriter_.getSourceMgr(); }
    const clang::LangOptions& getLangOpts() const { return rewriter_.getLangOpts(); }
    clang::RewriteBuffer& getEditBuffer(clang::FileID fid) { return rewriter_.getEditBuffer(fid); }

    bool isReplaced(clang::SourceRange range) const;

private:
    clang::Rewriter &rewriter_;
    struct Range { unsigned begin, end; };
    std::vector<Range> ranges_;

    void markReplaced(clang::SourceRange range);
    void markReplaced(clang::CharSourceRange range);
};

#endif

