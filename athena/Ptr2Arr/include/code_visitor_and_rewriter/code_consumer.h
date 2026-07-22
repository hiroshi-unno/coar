#ifndef CODE_CONSUMER_H
#define CODE_CONSUMER_H

#include <sstream>
#include <memory>
#include "clang/Frontend/CompilerInstance.h"
#include "code_visitor_and_rewriter.h"

using namespace clang;

class CodeConsumer : public clang::ASTConsumer {
public:
    explicit CodeConsumer(ASTContext *Context, std::unique_ptr<TrackingRewriter> TheRewriter, std::vector<MemorySet>& memorySets, std::vector<PointsToString>& pointsToStrings, const std::map<std::string, std::vector<std::string>>& functionReturnMap)
        : TheRewriter_(std::move(TheRewriter)), VisitorAndRewriter(Context, *TheRewriter_, memorySets, pointsToStrings, functionReturnMap) {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context);

private:
    std::unique_ptr<TrackingRewriter> TheRewriter_;
    CodeVisitorAndRewriter VisitorAndRewriter;
};

#endif //CODE_CONSUMER_H