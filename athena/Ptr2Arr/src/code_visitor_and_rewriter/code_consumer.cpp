#include "../../include/code_visitor_and_rewriter/code_consumer.h"
#include <filesystem>
#include <fstream>
#include <regex>
#include <sstream>
#include <algorithm>
#include <vector>

#include "clang/AST/RecursiveASTVisitor.h"

namespace {
// The C type an SV-COMP nondeterministic-value function returns, read from its name, or the empty
// string for a name whose type the convention does not fix by name alone (typedef-named results
// such as loff_t, and anything unknown), which is then left alone.
std::string NondetReturnType(const std::string &name) {
    static const std::vector<std::pair<std::string, std::string>> table = {
        {"bool", "_Bool"},          {"char", "char"},
        {"uchar", "unsigned char"}, {"short", "short"},
        {"ushort", "unsigned short"}, {"int", "int"},
        {"uint", "unsigned int"},   {"unsigned", "unsigned int"},
        {"long", "long"},           {"ulong", "unsigned long"},
        {"longlong", "long long"},  {"ulonglong", "unsigned long long"},
    };
    const std::string prefix = "__VERIFIER_nondet_";
    if (name.rfind(prefix, 0) != 0) return "";
    const std::string suffix = name.substr(prefix.size());
    for (const auto &entry : table)
        if (entry.first == suffix) return entry.second;
    return "";
}

// Collects, in order of first call, the __VERIFIER_nondet_<t> functions the program calls without
// declaring them. Such a call is an implicit declaration: C gives the function the type `int ()`,
// so the compiled call returns a 32-bit int whatever <t> is, and every later pass that reads the
// call's type (the IR-level type annotation, the rewrite of a declared nondet function's result
// type) sees a different program from the one a declared call gives. A declaration is all that
// differs, so supplying it from the name makes the program the one the convention means.
class UndeclaredNondetCollector : public clang::RecursiveASTVisitor<UndeclaredNondetCollector> {
public:
    std::vector<std::string> names;
    bool VisitCallExpr(clang::CallExpr *CE) {
        const clang::FunctionDecl *FD = CE->getDirectCallee();
        if (!FD) return true;
        const std::string name = FD->getNameAsString();
        if (NondetReturnType(name).empty()) return true;
        for (const clang::FunctionDecl *R : FD->redecls())
            if (!R->isImplicit()) return true;
        if (std::find(names.begin(), names.end(), name) == names.end()) names.push_back(name);
        return true;
    }
};

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

    UndeclaredNondetCollector undeclaredNondets;
    undeclaredNondets.TraverseDecl(TU);

    VisitorAndRewriter.runPreCheck(TU);
    VisitorAndRewriter.TraverseDecl(TU);
    VisitorAndRewriter.applyDeferredInsertions();

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

    // Inserted before the reach_error declaration below, which is then placed above them: the
    // output is then the one the same program with these declarations written at its top gives.
    std::string nondetDecls;
    for (const std::string &name : undeclaredNondets.names)
        nondetDecls += "extern " + NondetReturnType(name) + " " + name + "(void);\n";
    content.insert(0, nondetDecls);

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