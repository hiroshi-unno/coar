#ifndef TRACKING_REWRITER_H
#define TRACKING_REWRITER_H

#include "clang/Rewrite/Core/Rewriter.h"
#include <vector>

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

