#include "../../include/code_visitor_and_rewriter/code_consumer.h"
#include <filesystem>
#include <fstream>
#include <regex>
#include <sstream>

namespace {
bool AddNoReturnAttributeToReachError(std::string &content) {
    const std::regex reachErrorNoReturnPattern(
        R"((?:noreturn|__noreturn__)[^\n;{]*\breach_error\b|\breach_error\s*\([^)]*\)[^\n;{]*(?:noreturn|__noreturn__))");
    if (std::regex_search(content, reachErrorNoReturnPattern)) {
        return true;
    }

    const std::regex reachErrorDeclPattern(
        R"((\b(?:(?:extern|static)\s+)?void\s+reach_error\s*\([^)]*\))(\s*)([;{]))");
    std::string updated;
    std::size_t lastPos = 0;
    bool changed = false;

    for (std::sregex_iterator it(content.begin(), content.end(), reachErrorDeclPattern), end;
         it != end; ++it) {
        const std::smatch &match = *it;
        std::size_t matchStart = static_cast<std::size_t>(match.position());
        std::size_t matchEnd = matchStart + static_cast<std::size_t>(match.length());

        std::size_t lineStart = content.rfind('\n', matchStart);
        lineStart = (lineStart == std::string::npos) ? 0 : lineStart + 1;
        std::string currentLine = content.substr(lineStart, matchEnd - lineStart);
        if (currentLine.find("noreturn") != std::string::npos ||
            currentLine.find("__noreturn__") != std::string::npos) {
            continue;
        }

        updated.append(content, lastPos, matchStart - lastPos);
        updated += match[1].str();
        updated += " __attribute__((__noreturn__))";
        updated += match[2].str();
        updated += match[3].str();
        lastPos = matchEnd;
        changed = true;
    }

    if (changed) {
        updated.append(content, lastPos, std::string::npos);
        content = std::move(updated);
    }

    return changed;
}
}

void CodeConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    clang::TranslationUnitDecl *TU = Context.getTranslationUnitDecl();

    VisitorAndRewriter.runPreCheck(TU);
    VisitorAndRewriter.TraverseDecl(TU);

    std::error_code EC;
    auto outputPath = outputSourcePath;
    llvm::raw_fd_ostream stream(outputPath.string(), EC, llvm::sys::fs::OF_Text);
    TheRewriter_->getEditBuffer(TheRewriter_->getSourceMgr().getMainFileID()).write(stream);
    stream.close();

    std::ifstream in(outputPath);
    std::stringstream buf;
    buf << in.rdbuf();
    std::string content = buf.str();
    in.close();

    const std::string intr_func = "intr_strncpy (int dest, int src, size_t n){return strncpy(dest,src,n);}";
    size_t pos = content.find(intr_func);
    if (pos != std::string::npos) {
        content.erase(pos, intr_func.length());
    }

    if (VisitorAndRewriter.requiresReachErrorDeclaration()) {
        const std::string reachErrorDecl =
            "extern void reach_error(void) __attribute__((__noreturn__));\n";
        if (!AddNoReturnAttributeToReachError(content)) {
            content.insert(0, reachErrorDecl);
        }
    }

    pos = content.find("typedef unsigned int size_t;");
    if (pos != std::string::npos) {
        pos = content.find('\n', pos) + 1;
        content.insert(pos, "#include \"ptr2arr_runtime_stubs.h\"\n");
    }

    std::ofstream out(outputPath);
    out << content;
    out.close();

    const std::filesystem::path stubSrc = executableDirectory / "ptr2arr_runtime_stubs.h";
    const std::filesystem::path stubDst = outputDirectory / "ptr2arr_runtime_stubs.h";
    std::filesystem::copy_file(stubSrc, stubDst, std::filesystem::copy_options::overwrite_existing);
}