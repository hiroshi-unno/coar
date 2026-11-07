#include "clang/AST/ParentMapContext.h"
#include "clang/AST/ASTTypeTraits.h"
#include "../../include/code_visitor_and_rewriter/code_visitor_and_rewriter.h"
#include "llvm/Support/CommandLine.h"

static llvm::cl::OptionCategory Ptr2ArrCategory("Ptr2Arr Options");

static llvm::cl::opt<bool> MemorySafety(
    "memory-safety",
    llvm::cl::desc("Enable memory safety rewrite rules"),
    llvm::cl::init(false),
    llvm::cl::cat(Ptr2ArrCategory)
);

static llvm::cl::opt<bool> AssumeSafety(
    "assume-safety",
    llvm::cl::desc("Assume memory safety: an execution ends at its first access outside the block it points into"),
    llvm::cl::init(false),
    llvm::cl::cat(Ptr2ArrCategory)
);

// Both safety modes give each pointer the base and the length of the block it points into (the
// `__Ptr2Arr_base_*` and `__Ptr2Arr_len_*` globals) and route every access through
// `safe_idx_memoryN`; they differ only in what an access outside those bounds does. Under
// --memory-safety it calls `reach_error()`, so a safety checker asked whether that call is reachable
// decides memory safety. Under --assume-safety it ends the execution normally, so a termination
// checker's YES on the rewritten program says that every execution staying in bounds terminates,
// and its NO exhibits one that stays in bounds and does not. Together with a proof that the
// --memory-safety program never reaches `reach_error()`, that is a verdict on the input, as far as
// the rewriting itself is faithful.
static bool tracksBounds() { return MemorySafety || AssumeSafety; }

bool safetyModesConflict() { return MemorySafety && AssumeSafety; }

// A memory set read at more than one type is addressed by bytes: its cells are `unsigned char`, and
// it is read and written through the `load_memoryK_T` and `store_memoryK_T` helpers.
static bool isByteAddressed(const MemorySet &set) {
    return set.dataType == "unsigned char" && set.accessedTypes.size() > 1;
}

// The bytes one element of type `T` takes in a byte-addressed set: one for a character type, four
// for anything else, which the model reads and writes through the 4-byte int helpers.
static int modelBytes(clang::QualType T) { return T->isCharType() ? 1 : 4; }

// `count` elements of type `T`, in the units of `set`: elements for an element-addressed set,
// bytes for a byte-addressed one.
static std::string modelCount(const std::string &count, clang::QualType T, const MemorySet &set) {
    if (!isByteAddressed(set)) return count;
    if (count == "1") return std::to_string(modelBytes(T));
    return "(" + count + ") * " + std::to_string(modelBytes(T));
}

// The size argument of an `alloca` or `malloc`, in the units of `set`. In an element-addressed set
// every `sizeof(T)` is 1. In a byte-addressed set it is the bytes the model touches for `T`, as in
// `modelBytes`; the argument is source text, so a `T` that is not a spelled character type counts
// four.
static std::string modelSize(const std::string &size, const MemorySet &set) {
    static const std::regex sizeofPattern("sizeof\\s*\\((.*?)\\)");
    static const std::regex charType("^\\s*(?:(?:signed|unsigned)\\s+)?char\\s*$");
    std::string out;
    std::size_t last = 0;
    for (auto it = std::sregex_iterator(size.begin(), size.end(), sizeofPattern); it != std::sregex_iterator(); ++it) {
        out += size.substr(last, it->position() - last);
        out += (isByteAddressed(set) && !std::regex_match((*it)[1].str(), charType)) ? "4" : "1";
        last = it->position() + it->length();
    }
    return out + size.substr(last);
}

// The name whose `__Ptr2Arr_base_*` and `__Ptr2Arr_len_*` describe the block the pointer value `E`
// points into: `q` for `q`, `q + i`, `q - i`, `&q[i]` and `&q`, with the `_index` suffix when `q` is
// itself a block (a pointee) rather than a pointer. Pointer arithmetic does not move the block, so
// the base and the length are the operand's, unshifted. Empty when no tracked variable is found.
static std::string boundsOwner(const clang::Expr *E, const std::vector<MemorySet> &memorySets) {
    E = E->IgnoreParenCasts();
    if (const auto *DRE = llvm::dyn_cast<clang::DeclRefExpr>(E)) {
        std::string name = DRE->getDecl()->getNameAsString();
        auto named = [&name](const ScopedPointer &s) { return s.pointerName == name; };
        for (const auto &ms : memorySets)
            if (std::find_if(ms.pointers.begin(), ms.pointers.end(), named) != ms.pointers.end()) return name;
        for (const auto &ms : memorySets)
            if (std::find_if(ms.pointees.begin(), ms.pointees.end(), named) != ms.pointees.end()) return name + "_index";
        return "";
    }
    if (const auto *UO = llvm::dyn_cast<clang::UnaryOperator>(E)) {
        if (UO->getOpcode() != clang::UO_AddrOf) return "";
        const clang::Expr *sub = UO->getSubExpr()->IgnoreParenCasts();
        if (const auto *ASE = llvm::dyn_cast<clang::ArraySubscriptExpr>(sub)) return boundsOwner(ASE->getBase(), memorySets);
        if (llvm::isa<clang::DeclRefExpr>(sub)) return boundsOwner(sub, memorySets);
        return "";
    }
    if (const auto *BO = llvm::dyn_cast<clang::BinaryOperator>(E)) {
        if (BO->getOpcode() != clang::BO_Add && BO->getOpcode() != clang::BO_Sub) return "";
        if (BO->getLHS()->getType()->isPointerType() || BO->getLHS()->getType()->isArrayType()) return boundsOwner(BO->getLHS(), memorySets);
        if (BO->getOpcode() == clang::BO_Add && (BO->getRHS()->getType()->isPointerType() || BO->getRHS()->getType()->isArrayType())) return boundsOwner(BO->getRHS(), memorySets);
    }
    return "";
}


std::string getTypeSuffix(clang::QualType type) {
    if (type->isPointerType() || type->isArrayType()) return "int";
    std::string typeStr = type.getAsString();
    if (typeStr.find("char") != std::string::npos) return "char";
    if (typeStr.find("float") != std::string::npos) return "float";
    if (typeStr.find("double") != std::string::npos) return "double";
    return "int";
}
// Bounds that decide nothing on their own, for a pointer whose block cannot be found: under
// --memory-safety a length of 0 reports every access through it, under --assume-safety the whole
// memory array cuts none. Every memory array has the size of the first.
static void unknownBounds(std::string &len, std::string &base) {
    len = AssumeSafety ? "MEMORY0_SIZE" : "0";
    base = "0";
}

clang::SourceLocation CodeVisitorAndRewriter::laterRecordLocation(const std::string &typeName, const clang::FunctionDecl *first) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    const clang::RecordDecl *found = lookupRecord(typeName);
    const clang::RecordDecl *record = found ? found->getDefinition() : nullptr;
    if (!record || !SM.isInMainFile(SM.getExpansionLoc(record->getBeginLoc()))) return clang::SourceLocation();
    clang::SourceLocation recordEnd = SM.getExpansionLoc(record->getEndLoc());
    if (!SM.isBeforeInTranslationUnit(SM.getExpansionLoc(first->getBeginLoc()), recordEnd)) return clang::SourceLocation();
    for (auto *D : Context->getTranslationUnitDecl()->decls()) {
        const auto *F = llvm::dyn_cast<clang::FunctionDecl>(D);
        if (!F || !F->doesThisDeclarationHaveABody()) continue;
        clang::SourceLocation begin = SM.getExpansionLoc(F->getBeginLoc());
        if (SM.isInMainFile(begin) && SM.isBeforeInTranslationUnit(recordEnd, begin)) return begin;
    }
    return clang::SourceLocation();
}

// The struct or union `typeName` names (`struct S`, `union U`, or a typedef of one), looked up in the
// translation unit's scope, which also holds a tag first named inside another declaration
// (`struct L4 { struct L5 *down; };` declares `struct L5`); null when it names none.
const clang::RecordDecl *CodeVisitorAndRewriter::lookupRecord(const std::string &typeName) {
    clang::TranslationUnitDecl *TU = Context->getTranslationUnitDecl();
    for (const char *keyword : {"struct ", "union "}) {
        std::string prefix = keyword;
        if (typeName.compare(0, prefix.size(), prefix) != 0) continue;
        clang::IdentifierInfo &name = Context->Idents.get(typeName.substr(prefix.size()));
        for (clang::NamedDecl *ND : TU->lookup(clang::DeclarationName(&name))) {
            if (const auto *RD = llvm::dyn_cast<clang::RecordDecl>(ND)) return RD;
        }
        return nullptr;
    }
    for (auto *D : TU->decls()) {
        const auto *TD = llvm::dyn_cast<clang::TypedefNameDecl>(D);
        if (!TD || TD->getNameAsString() != typeName) continue;
        if (const auto *RT = TD->getUnderlyingType()->getAs<clang::RecordType>()) return RT->getDecl();
    }
    return nullptr;
}

namespace {
// The spelling (`struct S`, `union U`) of every struct and union definition of a translation unit,
// wherever it is written, inside a function or another record included.
class RecordDefinitions : public clang::RecursiveASTVisitor<RecordDefinitions> {
public:
    explicit RecordDefinitions(clang::ASTContext &context) : context(context) {}
    bool VisitRecordDecl(clang::RecordDecl *RD) {
        if (RD->isThisDeclarationADefinition()) names.insert(context.getRecordType(RD).getAsString());
        return true;
    }
    std::set<std::string> names;
private:
    clang::ASTContext &context;
};
}

bool CodeVisitorAndRewriter::undefinedRecord(const std::string &typeName) {
    if (typeName.compare(0, 7, "struct ") == 0 || typeName.compare(0, 6, "union ") == 0) {
        RecordDefinitions definitions(*Context);
        definitions.TraverseDecl(Context->getTranslationUnitDecl());
        return definitions.names.count(typeName) == 0;
    }
    const clang::RecordDecl *RD = lookupRecord(typeName);
    return RD && !RD->getDefinition();
}

void CodeVisitorAndRewriter::applyDeferredInsertions() {
    for (const auto &[loc, text] : deferredInsertions) {
        if (TheRewriter.InsertTextBefore(loc, text)) {
            llvm::errs() << "[Ptr2Arr] Error: a memory array could not be declared after its element type\n";
        }
    }
    deferredInsertions.clear();
}

std::string CodeVisitorAndRewriter::trackedReturnName(const clang::CallExpr *CE) {
    const clang::FunctionDecl *callee = CE->getDirectCallee();
    if (!callee) return "";
    const clang::FunctionDecl *def = callee->getDefinition();
    if (!def || !def->getReturnType()->isPointerType()) return "";
    if (!TheRewriter.getSourceMgr().isInMainFile(def->getLocation())) return "";
    return def->getNameAsString();
}

bool CodeVisitorAndRewriter::boundsOf(const clang::Expr *E, std::string &len, std::string &base) {
    std::string owner = boundsOwner(E, memorySets);
    if (!owner.empty()) {
        len = "__Ptr2Arr_len_" + owner;
        base = "__Ptr2Arr_base_" + owner;
        return true;
    }
    if (E->isNullPointerConstant(*Context, clang::Expr::NPC_ValueDependentIsNull)) {
        // A null pointer points into no block, so every access through it is out of bounds.
        len = "0";
        base = "0";
        return true;
    }
    const clang::Expr *S = E->IgnoreParenCasts();
    if (const auto *CE = llvm::dyn_cast<clang::CallExpr>(S)) {
        std::string f = trackedReturnName(CE);
        if (f.empty()) return false;
        len = "__Ptr2Arr_ret_len_" + f;
        base = "__Ptr2Arr_ret_base_" + f;
        return true;
    }
    if (const auto *BO = llvm::dyn_cast<clang::BinaryOperator>(S)) {
        if (BO->getOpcode() == clang::BO_Add || BO->getOpcode() == clang::BO_Sub) {
            if (BO->getLHS()->getType()->isPointerType()) return boundsOf(BO->getLHS(), len, base);
            if (BO->getOpcode() == clang::BO_Add && BO->getRHS()->getType()->isPointerType()) return boundsOf(BO->getRHS(), len, base);
        }
    }
    return false;
}

// `return e;` in a function that returns a pointer records the bounds of the block `e` points into:
// `return (__Ptr2Arr_ret_val_f = e', __Ptr2Arr_ret_len_f = len, __Ptr2Arr_ret_base_f = base,
// __Ptr2Arr_ret_val_f);`. The value is computed first, so `e` may itself be a call whose bounds are
// taken over. A caller reads the three right after the call returns.
bool CodeVisitorAndRewriter::VisitReturnStmt(clang::ReturnStmt *RS) {
    if (isPreCheckPhase || !tracksBounds() || memorySets.empty() || !currentFD) return true;
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    const clang::Expr *value = RS->getRetValue();
    if (!value || !SM.isInMainFile(SM.getExpansionLoc(RS->getBeginLoc()))) return true;
    if (!currentFD->getReturnType()->isPointerType()) return true;

    clang::CharSourceRange range = clang::CharSourceRange::getTokenRange(
        SM.getExpansionLoc(value->getBeginLoc()), SM.getExpansionLoc(value->getEndLoc()));
    bool isNull = value->isNullPointerConstant(*Context, clang::Expr::NPC_ValueDependentIsNull);
    std::string text = isNull ? "0" : TheRewriter.getRewrittenText(range);
    if (text.empty()) return true;
    std::string len, base;
    if (!boundsOf(value, len, base)) unknownBounds(len, base);

    std::string f = currentFD->getNameAsString();
    std::string replacement = "(__Ptr2Arr_ret_val_" + f + " = " + text + ", __Ptr2Arr_ret_len_" + f + " = " + len +
                              ", __Ptr2Arr_ret_base_" + f + " = " + base + ", __Ptr2Arr_ret_val_" + f + ")";
    if (TheRewriter.ReplaceText(range, replacement)) {
        llvm::errs() << "[Ptr2Arr] Warning: the bounds of a pointer returned by " << f << " could not be recorded\n";
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitFieldDecl(clang::FieldDecl *FD) {
    if (isPreCheckPhase) return true;
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(FD->getBeginLoc())) {
        if (FD->getType()->isPointerType()) {
            std::string fieldName = FD->getNameAsString();

            if (tracksBounds()) {
                std::string textToReplace = "int " + fieldName;
                TheRewriter.ReplaceText(FD->getSourceRange(), textToReplace);
                WriteToFile("StructureField, " + fieldName);

            } else {
                // llvm::outs() << "Pointer Declaration as Structure Field" << "\n";
                std::string textToReplace = "int " + fieldName;
                TheRewriter.ReplaceText(FD->getSourceRange(), textToReplace);

                WriteToFile("StructureField, " + fieldName);
            }
        }
    }
    return true;
}




bool CodeVisitorAndRewriter::TraverseFunctionDecl(clang::FunctionDecl *FD) {
    if (isPreCheckPhase) {
        return clang::RecursiveASTVisitor<CodeVisitorAndRewriter>::TraverseFunctionDecl(FD);
    }
    // Set currentFunction to the function being traversed,
    // and restore it after traversal to handle nested functions correctly
    std::string savedFunction = currentFunction;
    clang::FunctionDecl *savedFD = currentFD;
    currentFunction = FD->getNameAsString();
    currentFD = FD;

    bool result = clang::RecursiveASTVisitor<CodeVisitorAndRewriter>::TraverseFunctionDecl(FD);

    currentFunction = savedFunction;
    currentFD = savedFD;
    return result;
}

std::string getMemorySetType(std::string dataType) {
    if (dataType.empty()) {
        std::cerr << "Error: Empty data type in memory set\n";
        exit(1);
    }

    // A set whose pointers are all `void *` is never read or written through `void` itself, and an
    // array of `void` does not compile, so its cells are ints, like those of any pointer value.
    if (dataType.back() == '*' || dataType == "void" || dataType == "const void") {
        return "int";
    }else {
        return dataType;
    }

}

bool CodeVisitorAndRewriter::VisitFunctionDecl(clang::FunctionDecl *FD) {
    if (isPreCheckPhase) return true;
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(FD->getBeginLoc())) {
        if (FD->hasBody()) {
            currentFunction = FD->getNameAsString();

            if (currentFunction == "main") {
                mainFunctionStartLoc = FD->getBody()->getBeginLoc().getLocWithOffset(1);

                // initialize memory sets for string literals at the beginning of main function
                std::string textToInsert;

                for (const auto& pts : pointsToStrings) {
                    for (size_t i = 0; i < memorySets.size(); ++i) {
                        auto it = std::find_if(memorySets[i].pointees.begin(), memorySets[i].pointees.end(), [&pts](const ScopedPointer& p) {
                            return p.pointerName == pts.llvmVarName && p.functionName == "";
                        });

                        if (it != memorySets[i].pointees.end()) {
                            std::string memIdx = std::to_string(i);
                            int len = pts.content.length();

                            textToInsert += "\n    " + pts.varName + " = allocate_memory" + memIdx + "(" + std::to_string(len) + ");\n";
                            if (tracksBounds()) {
                                textToInsert += "    __Ptr2Arr_base_" + pts.varName + " = " + pts.varName + ";\n";
                            }

                            for (int j = 0; j < len; ++j) {
                                unsigned char c = pts.content[j];
                                std::string charRepr;

                                // escape special characters for better readability in the generated code
                                switch (c) {
                                    case '\n': charRepr = "\\n";  break;
                                    case '\r': charRepr = "\\r";  break;
                                    case '\t': charRepr = "\\t";  break;
                                    case '\\': charRepr = "\\\\"; break;
                                    case '\'': charRepr = "\\'";  break;
                                    case '\"': charRepr = "\\\""; break;
                                    default:
                                        // escape printable characters as-is, otherwise use hexadecimal notation (\xHH)
                                        if (std::isprint(c)) {
                                            charRepr = std::string(1, c);
                                        } else {
                                            std::stringstream ss;
                                            ss << "\\x" << std::hex << std::setw(2) << std::setfill('0') << (int)c;
                                            charRepr = ss.str();
                                        }
                                        break;
                                }
                                textToInsert += "    memory" + memIdx + "[" + pts.varName + " + " + std::to_string(j) + "] = '" + charRepr + "';\n";
                            }
                        }
                    }
                }
                TheRewriter.InsertTextAfterToken(mainFunctionStartLoc, textToInsert);
            }

            // llvm::outs() << "Pointer as Function Return Type" << "\n";
            if (FD->getReturnType()->isPointerType()) {
                std::string textToReplace = "int ";
                TheRewriter.ReplaceText(FD->getReturnTypeSourceRange(), textToReplace);

                WriteToFile("Function, " + currentFunction);
            }

            // llvm::outs() << "Pointer or Pointee Declaration as Function Parameter" << "\n";
            for (clang::ParmVarDecl *param : FD->parameters()) {
                std::string paramName = param->getNameAsString();
                clang::QualType paramType = param->getType();
                ScopedPointer paramSp = {currentFunction, paramName};
                if (paramType->isPointerType() || paramType->isArrayType()) {
                    for (size_t i = 0; i < memorySets.size(); ++i) {
                        if (std::find(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), paramSp) != memorySets[i].pointers.end()){
                            std::string textToReplace = "int " + paramName;
                            TheRewriter.ReplaceText(param->getSourceRange(), textToReplace);

                            WriteToFile("FunctionParameter, " + currentFunction + ", " + paramName);
                            break;
                        }
                        if (std::find(memorySets[i].pointees.begin(), memorySets[i].pointees.end(), paramSp) != memorySets[i].pointees.end()) {
                            std::string textToReplace = "int " + paramName + "_index";
                            TheRewriter.ReplaceText(param->getSourceRange(), textToReplace);

                            WriteToFile("FunctionParameter, " + currentFunction + ", " + paramName + "_index");
                            break;
                        }
                    }
                }
            }

            if (isFirstFunction) {
                std::string textToInsert;
                if (AssumeSafety && !memorySets.empty()) {
                    // The assumption ends an execution with `_Exit` rather than `exit`, because some
                    // inputs define `exit` themselves, as SV-COMP's `void exit(int s) { _EXIT: goto
                    // _EXIT; }`, which would turn the end of an execution into a loop that never
                    // terminates; the C standard reserves `_Exit`, so no input may define it. The
                    // helper's name is Ptr2Arr's own because inputs define `__VERIFIER_assume`
                    // themselves, some with an `int` and some with a `_Bool` parameter, and a
                    // definition of ours would collide with either. llvm2kittel ends the run at the
                    // `unreachable` that follows a call to a noreturn function, so in the
                    // transition system a failed assumption is a terminating step.
                    textToInsert += "extern void _Exit(int) __attribute__((__noreturn__));\n"
                                    "void __Ptr2Arr_assume(int cond) {\n"
                                    "    if (!cond) _Exit(0);\n"
                                    "}\n\n";
                    WriteToFile("Function, __Ptr2Arr_assume");
                    WriteToFile("FunctionParameter, __Ptr2Arr_assume, cond");
                }
                for (size_t i = 0; i < memorySets.size(); ++i) {

                    std::string convertedDatatype = getMemorySetType(memorySets[i].dataType);
                    std::string memIdx = std::to_string(i);

                    // A struct or union no declaration completes (only pointers to it are used) has
                    // no object that is read or written, so its cells are ints.
                    if (undefinedRecord(convertedDatatype)) convertedDatatype = "int";

                    // The memory array of a struct or union defined after the first function
                    // definition (an input may define `exit` before its types) is declared instead
                    // right before the first function definition that follows the type's. Every
                    // function that reads or writes the array needs the type complete, so it comes
                    // later still; everything else in the prelude is independent of the type. The
                    // insertion is made after the whole traversal: that function's own rewrites (its
                    // return type) start at the same place, and a replacement made after an insertion
                    // there would count the inserted text in its length and erase it.
                    std::string memoryDecl = convertedDatatype + " memory" + memIdx + "[MEMORY" + memIdx + "_SIZE];\n";
                    clang::SourceLocation laterLoc = laterRecordLocation(convertedDatatype, FD);
                    if (laterLoc.isValid()) {
                        deferredInsertions.push_back({laterLoc, memoryDecl});
                        memoryDecl = "";
                    }

                    if (MemorySafety) {
                        reachErrorCallGenerated = true;
                        textToInsert += "#define MEMORY" + memIdx + "_SIZE 100000\n" +
                                        memoryDecl +
                                        "int memory" + memIdx + "_freeIndex = 1;\n\n";
                        if(hasFreeInCode){
                             textToInsert += "int memory" + memIdx + "_free" + "[MEMORY" + memIdx + "_SIZE];\n"
                                            "int allocate_memory" + memIdx + "(int size) {\n"
                                            "   int allocatedIndex = memory" + memIdx + "_freeIndex;\n"
                                            "   memory" + memIdx + "_freeIndex = memory" + memIdx + "_freeIndex + size;\n"
                                            "   return allocatedIndex;\n"
                                            "}\n\n"

                                            "int free_memory" + memIdx + "(int base_idx,int ptr_idx,int len){\n"
                                            "   if(base_idx != ptr_idx){\n"
                                            "       reach_error();\n"
                                            "       return 0;\n"
                                            "   }\n"
                                            "   if(memory" + memIdx + "_free" + "[base_idx] == 1){\n"
                                            "       reach_error();\n"
                                            "       return 0;\n"
                                            "   }\n"
                                            "   memory" + memIdx + "_free" + "[base_idx] = 1;\n"
                                            "   return 0;\n"
                                            "}\n\n"

                                            "int safe_idx_memory" + memIdx + "(int base_idx, int ptr_idx, int idx, int len) {\n"
                                            "   if (!(0 <= (ptr_idx - base_idx + idx) && (ptr_idx - base_idx + idx) < len)) {\n"
                                            "       reach_error();\n"
                                            "       return 0;\n"
                                            "   }\n"
                                            "   if(memory" + memIdx + "_free" + "[base_idx] == 1){\n"
                                            "       reach_error();\n"
                                            "       return 0;\n"
                                            "   }\n"
                                            "   return ptr_idx + idx;\n"
                                            "}\n\n";


                        }else{
                            textToInsert += "int allocate_memory" + memIdx + "(int size) {\n"
                                            "   int allocatedIndex = memory" + memIdx + "_freeIndex;\n"
                                            "   memory" + memIdx + "_freeIndex = memory" + memIdx + "_freeIndex + size;\n"
                                            "   return allocatedIndex;\n"
                                            "}\n\n"

                                            "int safe_idx_memory" + memIdx + "(int base_idx, int ptr_idx, int idx, int len) {\n"
                                            "   if (!(0 <= (ptr_idx - base_idx + idx) && (ptr_idx - base_idx + idx) < len)) {\n"
                                            "       reach_error();\n"
                                            "       return 0;\n"
                                            "   }\n"
                                            "   return ptr_idx + idx;\n"
                                            "}\n\n";
                        }

                    } else if (AssumeSafety) {
                        // No `memoryN_free` table: a free is a no-op in this mode (see the rewrite
                        // of `free` below), so there is no freed block to look up.
                        textToInsert += "#define MEMORY" + memIdx + "_SIZE 100000\n" +
                                        memoryDecl +
                                        "int memory" + memIdx + "_freeIndex = 1;\n\n"
                                        "int allocate_memory" + memIdx + "(int size) {\n"
                                        "   int allocatedIndex = memory" + memIdx + "_freeIndex;\n"
                                        "   memory" + memIdx + "_freeIndex = memory" + memIdx + "_freeIndex + size;\n"
                                        "   return allocatedIndex;\n"
                                        "}\n\n"

                                        "int safe_idx_memory" + memIdx + "(int base_idx, int ptr_idx, int idx, int len) {\n"
                                        "   __Ptr2Arr_assume(0 <= (ptr_idx - base_idx + idx) && (ptr_idx - base_idx + idx) < len);\n"
                                        "   return ptr_idx + idx;\n"
                                        "}\n\n";

                    }else{
                        textToInsert += "#define MEMORY" + memIdx + "_SIZE 100000\n" +
                                        memoryDecl +
                                        "int memory" + memIdx + "_freeIndex = 1;\n"
                                        "int allocate_memory" + memIdx + "(int size) {\n"
                                        "   int allocatedIndex = memory" + memIdx + "_freeIndex;\n"
                                        "   memory" + memIdx + "_freeIndex = memory" + memIdx + "_freeIndex + size;\n"
                                        "   return allocatedIndex;\n"
                                        "}\n\n";
                    }


                    WriteToFile("Macro, MEMORY" + memIdx + "_SIZE");
                    WriteToFile("GlobalVariable, memory" + memIdx + "_freeIndex");
                    WriteToFile("Function, allocate_memory" + memIdx);
                    WriteToFile("FunctionParameter, allocate_memory" + memIdx + ", size");
                    WriteToFile("LocalVariable, allocate_memory" + memIdx + ", allocatedIndex");

                    if (memorySets[i].dataType == "unsigned char" && memorySets[i].accessedTypes.size() > 1) {
                        std::set<std::string> generatedTypes;
                        for (const std::string& type : memorySets[i].accessedTypes) {
                            std::string baseType = type;
                            if (baseType.back() == '*') {
                                baseType = "int";
                            }

                            if (generatedTypes.count(baseType)) {
                                continue;
                            }
                            generatedTypes.insert(baseType);

                           if (baseType == "int") {
                                if (tracksBounds()) {
                                    textToInsert +=
                                        "int load_memory" + memIdx + "_int(int base_idx, int index, int len) {\n"
                                        "    int b0 = memory" + memIdx + "[safe_idx_memory" + memIdx + "(base_idx, index, 0, len)];\n"
                                        "    int b1 = memory" + memIdx + "[safe_idx_memory" + memIdx + "(base_idx, index, 1, len)];\n"
                                        "    int b2 = memory" + memIdx + "[safe_idx_memory" + memIdx + "(base_idx, index, 2, len)];\n"
                                        "    int b3 = memory" + memIdx + "[safe_idx_memory" + memIdx + "(base_idx, index, 3, len)];\n"
                                        "    return b0 + b1 * 256 + b2 * 256 * 256 + b3 * 256 * 256 * 256;\n"
                                        "}\n"
                                        "void store_memory" + memIdx + "_int(int base_idx, int index, int value, int len) {\n"
                                        "    unsigned int uvalue = (unsigned int)value;\n"
                                        "    memory" + memIdx + "[safe_idx_memory" + memIdx + "(base_idx, index, 0, len)] = (uvalue / 1) % 256;\n"
                                        "    memory" + memIdx + "[safe_idx_memory" + memIdx + "(base_idx, index, 1, len)] = (uvalue / 256) % 256;\n"
                                        "    memory" + memIdx + "[safe_idx_memory" + memIdx + "(base_idx, index, 2, len)] = (uvalue / (256 * 256)) % 256;\n"
                                        "    memory" + memIdx + "[safe_idx_memory" + memIdx + "(base_idx, index, 3, len)] = (uvalue / (256 * 256 * 256)) % 256;\n"
                                        "}\n";
                                }else {
                                    textToInsert +=
                                        "int load_memory" + memIdx + "_int(int index) {\n"
                                        "    int b0 = memory" + memIdx + "[index];\n"
                                        "    int b1 = memory" + memIdx + "[index + 1];\n"
                                        "    int b2 = memory" + memIdx + "[index + 2];\n"
                                        "    int b3 = memory" + memIdx + "[index + 3];\n"
                                        "    return b0 + b1 * 256 + b2 * 256 * 256 + b3 * 256 * 256 * 256;\n"
                                        "}\n"
                                        "void store_memory" + memIdx + "_int(int index, int value) {\n"
                                        "    unsigned int uvalue = (unsigned int)value;\n"
                                        "    memory" + memIdx + "[index] = (uvalue / 1) % 256;\n"
                                        "    memory" + memIdx + "[index + 1] = (uvalue / 256) % 256;\n"
                                        "    memory" + memIdx + "[index + 2] = (uvalue / (256 * 256)) % 256;\n"
                                        "    memory" + memIdx + "[index + 3] = (uvalue / (256 * 256 * 256)) % 256;\n"
                                        "}\n";
                                }
                            }
                            else if (baseType == "char") {
                                if (tracksBounds()) {
                                    textToInsert +=
                                        "char load_memory" + memIdx + "_char(int base_idx, int index, int len) {\n"
                                        "    return (char)memory" + memIdx + "[safe_idx_memory" + memIdx + "(base_idx, index, 0, len)];\n"
                                        "}\n"
                                        "void store_memory" + memIdx + "_char(int base_idx, int index, char value, int len) {\n"
                                        "    memory" + memIdx + "[safe_idx_memory" + memIdx + "(base_idx, index, 0, len)] = (unsigned char)value;\n"
                                        "}\n";
                                }else {
                                    textToInsert +=
                                        "char load_memory" + memIdx + "_char(int index) {\n"
                                        "    return (char)memory" + memIdx + "[index];\n"
                                        "}\n"
                                        "void store_memory" + memIdx + "_char(int index, char value) {\n"
                                        "    memory" + memIdx + "[index] = (unsigned char)value;\n"
                                        "}\n";
                                }
                            } else {
                                llvm::errs() << "[Ptr2Arr] Warning: accessed type '" << baseType << "' is not supported for automatic generation of load/store functions. Only 'int' and 'char' are supported.\n";
                            }
                        }
                    }
                    textToInsert += "\n";
                }

                // insert decrement functions for memory sets that require them
                for (const auto& [type, index] : requiredDecrementHelpers) {
                    std::string idxStr = std::to_string(index);

                    if (tracksBounds()) {
                        textToInsert += type + " post_decrement_memory" + idxStr + "_" + type + "(int base_idx, int index, int len) {\n";
                        textToInsert += "    " + type + " old_val = load_memory" + idxStr + "_" + type + "(base_idx, index, len);\n";
                        textToInsert += "    store_memory" + idxStr + "_" + type + "(base_idx, index, old_val - 1, len);\n";
                        textToInsert += "    return old_val;\n";
                        textToInsert += "}\n\n";
                    } else {
                        textToInsert += type + " post_decrement_memory" + idxStr + "_" + type + "(int index) {\n";
                        textToInsert += "    " + type + " old_val = load_memory" + idxStr + "_" + type + "(index);\n";
                        textToInsert += "    store_memory" + idxStr + "_" + type + "(index, old_val - 1);\n";
                        textToInsert += "    return old_val;\n";
                        textToInsert += "}\n\n";
                    }
                }

                // insert increment functions for memory sets that require them
                for (const auto& [type, index] : requiredIncrementHelpers) {
                    std::string idxStr = std::to_string(index);

                    if (tracksBounds()) {
                        textToInsert += type + " post_increment_memory" + idxStr + "_" + type + "(int base_idx, int index, int len) {\n";
                        textToInsert += "    " + type + " old_val = load_memory" + idxStr + "_" + type + "(base_idx, index, len);\n";
                        textToInsert += "    store_memory" + idxStr + "_" + type + "(base_idx, index, old_val + 1, len);\n";
                        textToInsert += "    return old_val;\n";
                        textToInsert += "}\n\n";
                    } else {
                        textToInsert += type + " post_increment_memory" + idxStr + "_" + type + "(int index) {\n";
                        textToInsert += "    " + type + " old_val = load_memory" + idxStr + "_" + type + "(index);\n";
                        textToInsert += "    store_memory" + idxStr + "_" + type + "(index, old_val + 1);\n";
                        textToInsert += "    return old_val;\n";
                        textToInsert += "}\n\n";
                    }
                }

                if (tracksBounds()) {
                    textToInsert += "// Global meta variables for pointer tracking\n";

                    std::set<std::string> declaredMetaVars;

                    for (size_t i = 0; i < memorySets.size(); ++i) {
                        for (const auto& sp : memorySets[i].pointers) {
                            std::string lenVar = "__Ptr2Arr_len_" + sp.pointerName;
                            std::string baseVar = "__Ptr2Arr_base_" + sp.pointerName;

                            if (declaredMetaVars.find(lenVar) == declaredMetaVars.end()) {
                                textToInsert += "int " + lenVar + ";\n";
                                textToInsert += "int " + baseVar + ";\n";

                                declaredMetaVars.insert(lenVar);
                                declaredMetaVars.insert(baseVar);

                                WriteToFile("GlobalVariable, " + lenVar);
                                WriteToFile("GlobalVariable, " + baseVar);
                            }
                        }

                        for (const auto& sp : memorySets[i].pointees) {
                            std::string lenVar = "__Ptr2Arr_len_" + sp.pointerName + "_index";
                            std::string baseVar = "__Ptr2Arr_base_" + sp.pointerName + "_index";

                            if (declaredMetaVars.find(lenVar) == declaredMetaVars.end()) {
                                textToInsert += "int " + lenVar + ";\n";
                                textToInsert += "int " + baseVar + ";\n";

                                declaredMetaVars.insert(lenVar);
                                declaredMetaVars.insert(baseVar);

                                WriteToFile("GlobalVariable, " + lenVar);
                                WriteToFile("GlobalVariable, " + baseVar);
                            }
                        }
                    }

                    // A function of the main file that returns a pointer records the bounds of the
                    // block it returns (`__Ptr2Arr_ret_len_f`, `__Ptr2Arr_ret_base_f`), and the value
                    // itself (`__Ptr2Arr_ret_val_f`), from which a call's result takes them.
                    std::set<std::string> declaredReturns;
                    for (auto *D : Context->getTranslationUnitDecl()->decls()) {
                        const auto *F = llvm::dyn_cast<clang::FunctionDecl>(D);
                        if (!F || !F->doesThisDeclarationHaveABody() || !F->getReturnType()->isPointerType()) continue;
                        if (!SM.isInMainFile(F->getLocation())) continue;
                        std::string f = F->getNameAsString();
                        if (!declaredReturns.insert(f).second) continue;
                        for (const char *what : {"len", "base", "val"}) {
                            std::string var = std::string("__Ptr2Arr_ret_") + what + "_" + f;
                            textToInsert += "int " + var + ";\n";
                            WriteToFile("GlobalVariable, " + var);
                        }
                    }
                    textToInsert += "\n";
                }

                // Insert declarations for converted string literals
                for (const auto& pointToString : pointsToStrings) {
                    textToInsert += "int " + pointToString.varName + ";\n";
                    WriteToFile("GlobalVariable, " + pointToString.varName);
                }

                // The prelude goes right before the first function definition. A memory array
                // whose element is a struct or a union must follow that type's definition, and an
                // input defines its types, its own and those of the headers it pastes in, before its
                // functions. The first declaration of the main file comes before all of them, and can
                // even sit inside another declaration: `typedef struct S {…} T;` declares the struct
                // first, after the `typedef`.
                clang::SourceLocation insertLoc = SM.getExpansionLoc(FD->getBeginLoc());
                if (TheRewriter.InsertTextBefore(insertLoc, textToInsert)) {
                    llvm::errs() << "[Ptr2Arr] Error: the generated declarations could not be inserted before " << currentFunction << "\n";
                }

                isFirstFunction = false;
            }
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitVarDecl(clang::VarDecl *VD) {
    if (isPreCheckPhase) return true;
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(VD->getBeginLoc())) {
        std::string varName = VD->getNameAsString();
        ScopedPointer varSp = {currentFunction, varName};
        int pointerId = -1;
        int pointeeId = -1;
        bool isPointer = false;
        bool isPointee = false;
        for (int i = 0; i < memorySets.size(); ++i) {
            if (std::find(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), varSp) != memorySets[i].pointers.end()) {
                pointerId = i;
                isPointer = true;
            }
            if (std::find(memorySets[i].pointees.begin(), memorySets[i].pointees.end(), varSp) != memorySets[i].pointees.end()) {
                pointeeId = i;
                isPointee = true;
            }
        }

        // The cell of a variable whose address is taken, in the units of its memory set.
        std::string cell = pointeeId != -1 ? modelCount("1", VD->getType(), memorySets[pointeeId]) : "1";

        bool isMulti = false;
        bool isFirstDecl = false;
        auto parents = VD->getASTContext().getParents(*VD);
        if (!parents.empty()) {
            if (const auto *DS = parents[0].get<clang::DeclStmt>()) {
                isMulti = !DS->isSingleDecl();
                if (isMulti && *DS->decl_begin() == VD) {
                    isFirstDecl = true;
                }
            }
        }

        if (isPointee && isPointer) {
            if (VD->hasGlobalStorage() && !VD->isStaticLocal()) {
                if (!VD->hasInit()) {
                    if (isMulti) {
                        TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                    } else {
                        if (tracksBounds()) {

                            std::string textToReplace = "int " + varName + "_index;\n"
                                                        "__Ptr2Arr_len_" + varName + "_index = 0;\n"
                                                        "__Ptr2Arr_base_" + varName + "_index = 0";
                            TheRewriter.ReplaceText(VD->getSourceRange(), textToReplace);
                        } else {
                            std::string textToReplace = "int " + varName + "_index";
                            TheRewriter.ReplaceText(VD->getSourceRange(), textToReplace);
                        }
                    }
                    WriteToFile("GlobalVariable, " + varName + "_index");
                }
            }

            else if (VD->isLocalVarDecl()) {
                if (VD->hasInit()) {
                    clang::Expr *initExpr = VD->getInit()->IgnoreParenImpCasts();
                    clang::SourceRange initExprRange = initExpr->getSourceRange();
                    std::string initExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(initExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                    bool isNull = VD->getInit()->isNullPointerConstant(*Context, clang::Expr::NPC_ValueDependentIsNull);
                    if (initExprStr == "NULL" || isNull) {
                        if (isMulti) {
                            TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                        } else {
                            if (tracksBounds()) {

                                std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n"
                                                            "    __Ptr2Arr_len_" + varName + "_index = " + cell + ";\n"
                                                            "    __Ptr2Arr_base_" + varName + "_index = " + varName + "_index";
                                if (memorySets[pointeeId].accessedTypes.size() > 1) {
                                    std::string suffix = getTypeSuffix(VD->getType());
                                    std::string initExprStrRewrite = TheRewriter.getRewrittenText(VD->getInit()->getSourceRange());
                                    textToReplace += "    store_memory" + std::to_string(pointeeId) + "_" + suffix + "(" + varName + "_index, " + initExprStrRewrite + ", __Ptr2Arr_len_" + varName + "_index);";
                                } else {
                                    textToReplace += "    memory" + std::to_string(pointeeId) + "[" + varName + "_index] = 0;";
                                }
                                TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                            } else {
                                if (memorySets[pointeeId].accessedTypes.size() > 1) {
                                    std::string suffix = getTypeSuffix(VD->getType());
                                    std::string initExprStrRewrite = TheRewriter.getRewrittenText(VD->getInit()->getSourceRange());
                                    std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n    store_memory" + std::to_string(pointeeId) + "_" + suffix + "(" + varName + "_index, " + initExprStrRewrite + ")";
                                    TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                                } else {
                                    std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n    memory" + std::to_string(pointeeId) + "[" + varName + "_index] = 0";
                                    TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                                }
                            }
                        }

                        if (tracksBounds() && !scopeStack.empty()) {
                            scopeStack.back().push_back({varName + "_index", pointeeId, false});
                        }
                        WriteToFile("LocalVariable, " + currentFunction + ", " + varName + "_index");
                    }

                    else if (initExprStr.find("alloca") != std::string::npos || initExprStr.find("malloc") != std::string::npos) {
                        bool isAlloca = (initExprStr.find("alloca") != std::string::npos);
                        std::string size;
                        std::regex allocPattern(".*(?:alloca|malloc)\\s*\\(\\s*(.*?)\\s*\\)");
                        std::smatch match;
                        if (std::regex_match(initExprStr, match, allocPattern)){
                            size = match[1].str();
                            size = modelSize(size, memorySets[pointeeId]);
                        }

                        std::string textToReplace;
                        if (tracksBounds()) {
                            textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + size + ");\n"
                                            "    __Ptr2Arr_len_" + varName + "_index = " + size + ";\n"
                                            "    __Ptr2Arr_base_" + varName + "_index = " + varName + "_index";
                        } else {
                            textToReplace = "int " + varName + "_index" + " = allocate_memory" + std::to_string(pointeeId) + "(" + size + ")";
                        }

                        if (tracksBounds() && isAlloca && !scopeStack.empty()) {
                            scopeStack.back().push_back({varName + "_index", pointeeId, true});
                        }

                        auto &SMExpansion = TheRewriter.getSourceMgr();
                        TheRewriter.ReplaceText(
                            clang::CharSourceRange::getCharRange(
                                SMExpansion.getExpansionLoc(VD->getBeginLoc()),
                                clang::Lexer::getLocForEndOfToken(initExpr->getEndLoc(), 0, SMExpansion, TheRewriter.getLangOpts())),
                            textToReplace);
                        WriteToFile("LocalVariable, " + currentFunction + ", " + varName + "_index");
                    }

                    else if (auto *UO = llvm::dyn_cast<clang::UnaryOperator>(initExpr)) {
                        if (UO->getOpcode() == clang::UO_AddrOf) {
                            clang::Expr *subExpr = UO->getSubExpr()->IgnoreParenImpCasts();
                            if (isa<clang::DeclRefExpr>(subExpr) || isa<clang::ArraySubscriptExpr>(subExpr)) {
                                if (isMulti) {
                                    TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                                } else {
                                    if (tracksBounds()) {
                                        std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n"
                                                                    "    __Ptr2Arr_len_" + varName + "_index = " + cell + ";\n"
                                                                    "    __Ptr2Arr_base_" + varName + "_index = " + varName + "_index";
                                        if (memorySets[pointeeId].accessedTypes.size() > 1) {
                                            std::string suffix = getTypeSuffix(VD->getType());
                                            std::string initExprStrRewrite = TheRewriter.getRewrittenText(VD->getInit()->getSourceRange());
                                            textToReplace += "    store_memory" + std::to_string(pointeeId) + "_" + suffix + "(" + varName + "_index, " + initExprStrRewrite + ", __Ptr2Arr_len_" + varName + "_inde);";
                                        } else {
                                            textToReplace += "    memory" + std::to_string(pointeeId) + "[" + varName + "_index];";
                                        }
                                        TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                                    } else {
                                        if (memorySets[pointeeId].accessedTypes.size() > 1) {
                                            std::string suffix = getTypeSuffix(VD->getType());
                                            std::string initExprStrRewrite = TheRewriter.getRewrittenText(VD->getInit()->getSourceRange());
                                            std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n    store_memory" + std::to_string(pointeeId) + "_" + suffix + "(" + varName + "_index, " + initExprStrRewrite + ");";
                                            TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                                        } else {
                                            std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n    memory" + std::to_string(pointeeId) + "[" + varName + "_index]";
                                            TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                                        }
                                    }
                                }

                                if (tracksBounds() && !scopeStack.empty()) {
                                    scopeStack.back().push_back({varName + "_index", pointeeId, false});
                                }
                                WriteToFile("LocalVariable, " + currentFunction + ", " + varName + "_index");
                            }
                        }
                    }

                    else if (initExpr->getType()->isArrayType()) {
                        if (isMulti) {
                            TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                        } else {
                            if (tracksBounds()) {
                                std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n"
                                                            "    __Ptr2Arr_len_" + varName + "_index = " + cell + ";\n"
                                                            "    __Ptr2Arr_base_" + varName + "_index = " + varName + "_index";
                                if (memorySets[pointeeId].accessedTypes.size() > 1) {
                                    std::string suffix = getTypeSuffix(VD->getType());
                                    std::string initExprStrRewrite = TheRewriter.getRewrittenText(VD->getInit()->getSourceRange());
                                    textToReplace += "    store_memory" + std::to_string(pointeeId) + "_" + suffix + "(" + varName + "_index, " + initExprStrRewrite + ", __Ptr2Arr_len_" + varName + "_index);";
                                } else {
                                    textToReplace += "    memory" + std::to_string(pointeeId) + "[" + varName + "_index];";
                                }
                                TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                            } else {
                                if (memorySets[pointeeId].accessedTypes.size() > 1) {
                                    std::string suffix = getTypeSuffix(VD->getType());
                                    std::string initExprStrRewrite = TheRewriter.getRewrittenText(VD->getInit()->getSourceRange());
                                    std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n    store_memory" + std::to_string(pointeeId) + "_" + suffix + "(" + varName + "_index, " + initExprStrRewrite + ");";
                                    TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                                } else {
                                    std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n    memory" + std::to_string(pointeeId) + "[" + varName + "_index]";
                                    TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                                }
                            }
                        }

                        if (tracksBounds() && !scopeStack.empty()) {
                            scopeStack.back().push_back({varName + "_index", pointeeId, false});
                        }
                        WriteToFile("LocalVariable, " + currentFunction + ", " + varName + "_index");
                    }

                    else {
                        if (isMulti) {
                            TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                        } else {
                            if (tracksBounds()) {
                                // The value as rewritten (`&x` is `x_index` by now), and the bounds of
                                // the block it points into, which pointer arithmetic does not move.
                                std::string rhsName = TheRewriter.getRewrittenText(VD->getInit()->getSourceRange());
                                if (rhsName.empty()) rhsName = initExprStr;
                                std::string len, base;
                                if (!boundsOf(VD->getInit(), len, base)) unknownBounds(len, base);
                                std::string textToReplace = "int " + varName + "_index = " + rhsName + ";\n"
                                                            "    __Ptr2Arr_len_" + varName + "_index = " + len + ";\n"
                                                            "    __Ptr2Arr_base_" + varName + "_index = " + base + ";\n";
                                TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                            } else {
                                std::string textToReplace = "int " + varName + "_index";
                                TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                            }
                        }
                        WriteToFile("LocalVariable, " + currentFunction + ", " + varName + "_index");
                    }
                }
                else {
                    if (isMulti) {
                        TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                    } else {
                        if (tracksBounds()) {
                            std::string textToReplace = "int " + varName + "_index;\n"
                                                        "    __Ptr2Arr_len_" + varName + "_index = 0;\n"
                                                        "    __Ptr2Arr_base_" + varName + "_index = 0";
                            TheRewriter.ReplaceText(VD->getSourceRange(), textToReplace);
                        } else {
                            std::string textToReplace = "int " + varName + "_index";
                            TheRewriter.ReplaceText(VD->getSourceRange(), textToReplace);
                        }
                    }
                    WriteToFile("LocalVariable, " + currentFunction + ", " + varName + "_index");
                }
            }
        }
        else if (isPointer) {
            if (VD->hasGlobalStorage() && !VD->isStaticLocal()) {
                if (!VD->hasInit()) {
                    if (isMulti) {
                        TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                    } else {
                        if (tracksBounds()) {
                            std::string textToReplace = "int " + varName + ";\n"
                                                        "__Ptr2Arr_len_" + varName + " = 0;\n"
                                                        "__Ptr2Arr_base_" + varName + " = 0;";
                            TheRewriter.ReplaceText(VD->getSourceRange(), textToReplace);
                        } else {
                            std::string textToReplace = "int " + varName;
                            TheRewriter.ReplaceText(VD->getSourceRange(), textToReplace);
                        }
                    }
                    WriteToFile("GlobalVariable, " + varName);
                }
            }

            else if (VD->isLocalVarDecl()) {
                if (VD->hasInit()) {
                    clang::Expr *initExpr = VD->getInit()->IgnoreParenImpCasts();
                    clang::SourceRange initExprRange = initExpr->getSourceRange();
                    std::string initExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(initExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                    bool isNull = VD->getInit()->isNullPointerConstant(*Context, clang::Expr::NPC_ValueDependentIsNull);
                    if (initExprStr == "NULL" || isNull) {
                        if (isMulti) {
                            TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                        } else {
                            if (tracksBounds()) {
                                std::string textToReplace = "int " + varName + " = 0;\n"
                                                            "    __Ptr2Arr_len_" + varName + " = 0;\n"
                                                            "    __Ptr2Arr_base_" + varName + " = 0;";
                                clang::CharSourceRange replaceRange = clang::CharSourceRange::getTokenRange(
                                    SM.getExpansionLoc(VD->getBeginLoc()),
                                    SM.getExpansionLoc(VD->getEndLoc())
                                );
                                TheRewriter.ReplaceText(replaceRange, textToReplace);
                            } else {
                                std::string textToReplace = "int " + varName + " = 0";
                                clang::CharSourceRange replaceRange = clang::CharSourceRange::getTokenRange(
                                    SM.getExpansionLoc(VD->getBeginLoc()),
                                    SM.getExpansionLoc(VD->getEndLoc())
                                );
                                TheRewriter.ReplaceText(replaceRange, textToReplace);
                            }
                        }
                        WriteToFile("LocalVariable, " + currentFunction + ", " + varName);
                    }

                    else if (initExprStr.find("alloca") != std::string::npos || initExprStr.find("malloc") != std::string::npos) {
                        bool isAlloca = (initExprStr.find("alloca") != std::string::npos);
                        std::string size;
                        std::regex allocPattern(".*(?:alloca|malloc)\\s*\\(\\s*(.*?)\\s*\\)");
                        std::smatch match;
                        if (std::regex_match(initExprStr, match, allocPattern)) {
                            size = match[1].str();
                            size = modelSize(size, memorySets[pointerId]);
                        }

                        std::string textToReplace;
                        if (tracksBounds()) {
                            textToReplace = "int " + varName + " = allocate_memory" + std::to_string(pointerId) + "(" + size + ");\n"
                                            "    __Ptr2Arr_len_" + varName + " = " + size + ";\n"
                                            "    __Ptr2Arr_base_" + varName + " = " + varName + "";
                        } else {
                            textToReplace = "int " + varName + " = allocate_memory" + std::to_string(pointerId) + "(" + size + ")";
                        }

                        if (tracksBounds() && isAlloca && !scopeStack.empty()) {
                            scopeStack.back().push_back({varName, pointerId, true});
                        }

                        auto &SMExpansion = TheRewriter.getSourceMgr();
                        TheRewriter.ReplaceText(
                            clang::CharSourceRange::getCharRange(
                                SMExpansion.getExpansionLoc(VD->getBeginLoc()),
                                clang::Lexer::getLocForEndOfToken(initExpr->getEndLoc(), 0, SMExpansion, TheRewriter.getLangOpts())),
                            textToReplace);
                        WriteToFile("LocalVariable, " + currentFunction + ", " + varName);
                    }

                    else {
                        if (isMulti) {
                            if (isFirstDecl) {
                                clang::CharSourceRange typeRange = clang::CharSourceRange::getCharRange(VD->getBeginLoc(), VD->getLocation());
                                TheRewriter.ReplaceText(typeRange, "int ");
                            } else {
                                TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                            }
                        } else {
                            if (tracksBounds()) {
                                // As above: the rewritten value and the unshifted bounds of its block.
                                std::string rhsName = TheRewriter.getRewrittenText(VD->getInit()->getSourceRange());
                                if (rhsName.empty()) rhsName = initExprStr;
                                std::string len, base;
                                if (!boundsOf(VD->getInit(), len, base)) unknownBounds(len, base);
                                std::string textToReplace = "int " + varName + " = " + rhsName + ";\n"
                                                            "    __Ptr2Arr_len_" + varName + " = " + len + ";\n"
                                                            "    __Ptr2Arr_base_" + varName + " = " + base + ";\n";
                                TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                            } else {
                                std::string textToReplace = "int " + varName;
                                TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                            }
                        }
                        WriteToFile("LocalVariable, " + currentFunction + ", " + varName);
                    }
                }
                else {
                    if (isMulti) {
                        if (isFirstDecl) {
                            clang::CharSourceRange typeRange = clang::CharSourceRange::getCharRange(VD->getBeginLoc(), VD->getLocation());
                            TheRewriter.ReplaceText(typeRange, "int ");
                        } else {
                            TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                        }
                    } else {
                        if (tracksBounds()) {
                            std::string textToReplace = "int " + varName + ";\n"
                                                        "    __Ptr2Arr_len_" + varName + " = 0;\n"
                                                        "    __Ptr2Arr_base_" + varName + " = 0";
                            TheRewriter.ReplaceText(VD->getSourceRange(), textToReplace);
                        } else {
                            std::string textToReplace = "int " + varName;
                            TheRewriter.ReplaceText(VD->getSourceRange(), textToReplace);
                        }
                    }
                    WriteToFile("LocalVariable, " + currentFunction + ", " + varName);
                }
            }
        }
        else if (isPointee) {
            if (VD->hasGlobalStorage() && !VD->isStaticLocal()) {
                if (!VD->hasInit()) {
                    std::string size = "1";
                    clang::QualType varType = VD->getType();
                    if (varType->isArrayType()) {
                        std::string arrayType = varType.getAsString();
                        size_t startBracket = arrayType.find('[');
                        size_t endBracket = arrayType.find(']', startBracket);
                        size = arrayType.substr(startBracket + 1, endBracket - startBracket - 1);
                        size = modelCount(size, varType->getAsArrayTypeUnsafe()->getElementType(), memorySets[pointeeId]);
                    } else {
                        size = cell;
                    }

                    if (tracksBounds()) {
                        std::string textToReplace = "int " + varName + "_index;\n"
                                                    "__Ptr2Arr_len_" + varName + "_index = " + size + ";\n"
                                                    "__Ptr2Arr_base_" + varName + "_index = 0";
                        TheRewriter.ReplaceText(VD->getSourceRange(), textToReplace);
                    } else {
                        std::string textToReplace = "int " + varName + "_index";
                        TheRewriter.ReplaceText(VD->getSourceRange(), textToReplace);
                    }

                    std::string textToInsert = "\n    " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + size + ");\n";
                    if (tracksBounds()) {
                        textToInsert += "    __Ptr2Arr_base_" + varName + "_index = " + varName + "_index;\n";
                    }
                    TheRewriter.InsertTextAfterToken(mainFunctionStartLoc, textToInsert);
                    WriteToFile("GlobalVariable, " + currentFunction + ", " + varName + "_index");
                }
            }

            else if (VD->isLocalVarDecl()) {
                if (VD->hasInit()) {
                    if (isMulti) {
                        TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                    } else {
                        if (tracksBounds()) {
                            std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n"
                                                        "    __Ptr2Arr_len_" + varName + "_index = " + cell + ";\n"
                                                        "    __Ptr2Arr_base_" + varName + "_index = " + varName + "_index;\n";
                            if (memorySets[pointeeId].accessedTypes.size() > 1) {
                                std::string suffix = getTypeSuffix(VD->getType());
                                std::string initExprStrRewrite = TheRewriter.getRewrittenText(VD->getInit()->getSourceRange());
                                textToReplace += "    store_memory" + std::to_string(pointeeId) + "_" + suffix + "(" + varName + "_index, " + initExprStrRewrite + ", __Ptr2Arr_len_" + varName + "_index);";
                            } else {
                                textToReplace += "    memory" + std::to_string(pointeeId) + "[" + varName + "_index];";
                            }
                            TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                        } else {
                            if (memorySets[pointeeId].accessedTypes.size() > 1) {
                                std::string suffix = getTypeSuffix(VD->getType());
                                std::string initExprStrRewrite = TheRewriter.getRewrittenText(VD->getInit()->getSourceRange());
                                std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n    store_memory" + std::to_string(pointeeId) + "_" + suffix + "(" + varName + "_index, " + initExprStrRewrite + ");";
                                TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                            } else {
                                std::string textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + cell + ");\n    memory" + std::to_string(pointeeId) + "[" + varName + "_index]";
                                TheRewriter.ReplaceText(clang::SourceRange(VD->getBeginLoc(), VD->getInit()->getEndLoc()), textToReplace);
                            }
                        }
                    }

                    if (tracksBounds() && !scopeStack.empty()) {
                        scopeStack.back().push_back({varName + "_index", pointeeId, false});
                    }
                    WriteToFile("LocalVariable, " + currentFunction + ", " + varName + "_index");
                }
                else {
                    std::string size = "1";
                    clang::QualType varType = VD->getType();
                    if (varType->isArrayType()) {
                        std::string arrayType = varType.getAsString();
                        size_t startBracket = arrayType.find('[');
                        size_t endBracket = arrayType.find(']', startBracket);
                        size = arrayType.substr(startBracket + 1, endBracket - startBracket - 1);
                        arrayVariableSizes[varName] = size;
                        size = modelCount(size, varType->getAsArrayTypeUnsafe()->getElementType(), memorySets[pointeeId]);
                    } else {
                        size = cell;
                    }
                    if (isMulti) {
                        TheRewriter.RemoveText(VD->getLocation().getLocWithOffset(-1), 1);
                    } else {
                        std::string textToReplace;
                        if (tracksBounds()) {
                            textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + size + ");\n"
                                            "    __Ptr2Arr_len_" + varName + "_index = " + size + ";\n"
                                            "    __Ptr2Arr_base_" + varName + "_index = " + varName + "_index;\n";
                        } else {
                            textToReplace = "int " + varName + "_index = allocate_memory" + std::to_string(pointeeId) + "(" + size + ");";
                        }
                        TheRewriter.ReplaceText(VD->getSourceRange(), textToReplace);
                    }

                    if (tracksBounds() && !scopeStack.empty()) {
                        scopeStack.back().push_back({varName + "_index", pointeeId, false});
                    }
                    WriteToFile("LocalVariable, " + currentFunction + ", " + varName + "_index");
                }
            }
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitDeclRefExpr(clang::DeclRefExpr *DRE) {
    if (isPreCheckPhase) return true;
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(DRE->getBeginLoc())) {
        if (TheRewriter.isReplaced(DRE->getSourceRange())) {
            return true;
        }
        if (clang::VarDecl *VD = llvm::dyn_cast<clang::VarDecl>(DRE->getDecl())) {
            std::string varName = VD->getNameAsString();
            ScopedPointer varSp = {currentFunction, varName};

            // Check if this variable is a pointee (needs _index suffix)
            int id = -1;
            bool isPointee = false;
            for (int i = 0; i < memorySets.size(); ++i) {
                if (std::find(memorySets[i].pointees.begin(), memorySets[i].pointees.end(), varSp) != memorySets[i].pointees.end()) {
                    id = i;
                    isPointee = true;
                    break;
                }
            }

            if (isPointee) {
                // Check if this DeclRefExpr is inside a sizeof expression
                // Walk up the parent chain to check
                auto checkParent = DRE;
                auto currentParents = Context->getParents(*checkParent);
                int depth = 0;
                while (!currentParents.empty() && depth < 10) {  // Max depth 10
                    // Check for sizeof expression
                    if (currentParents[0].get<clang::UnaryExprOrTypeTraitExpr>()) {
                        // This is inside sizeof, don't convert
                        return true;
                    }

                    // Check for address-of operator
                    if (const auto *UO = currentParents[0].get<clang::UnaryOperator>()) {
                        if (UO->getOpcode() == clang::UO_AddrOf) {
                            // Don't convert &x
                            return true;
                        }
                    }

                    // Move up one level
                    if (const auto *E = currentParents[0].get<clang::Expr>()) {
                        currentParents = Context->getParents(*E);
                    } else if (const auto *S = currentParents[0].get<clang::Stmt>()) {
                        currentParents = Context->getParents(*S);
                    } else {
                        break;
                    }
                    depth++;
                }

                // If DRE is inside array subscript expression, we should not convert it to index
                clang::DynTypedNode CurrentNode = clang::DynTypedNode::create(*DRE);

                // Walk up the parent chain to check if we are inside dereference or array subscript
                while (true){
                    auto parents = Context->getParents(CurrentNode);
                    if (parents.empty()) break;

                    if (const auto *UO = parents[0].get<clang::UnaryOperator>()) {
                        if (UO->getOpcode() == clang::UO_Deref) {
                            return true;
                        }
                    }

                    if (const auto *ASE = parents[0].get<clang::ArraySubscriptExpr>()) {
                        return true;
                    }

                    if (const auto *ParentExpr = parents[0].get<clang::Expr>()) {
                        if (isa<clang::CastExpr>(ParentExpr) || isa<clang::ParenExpr>(ParentExpr)) {
                            CurrentNode = parents[0];
                            continue;
                        }
                    }
                    break;
                }

                clang::QualType T = DRE->getType();
                std::string replacement;
                std::string idStr = std::to_string(id);

                if (memorySets[id].accessedTypes.size() > 1) {
                    if (tracksBounds()) {
                        replacement = "load_memory" + idStr + "_" + getTypeSuffix(T) + "(__Ptr2Arr_base_" + varName + "_index," + varName + "_index, __Ptr2Arr_len_" + varName + "_index)";
                    } else {
                        replacement = "load_memory" + idStr + "_" + getTypeSuffix(T) + "(" + varName + "_index)";
                    }
                } else if (T->isArrayType() || (T->isPointerType())) {
                    // If it's an array type, we want to add _index to the variable name
                    replacement = varName + "_index";
                } else {
                    if (tracksBounds()) {
                        replacement = "memory" + idStr + "[safe_idx_memory" + idStr + "( __Ptr2Arr_base_" + varName + "_index," + varName + "_index,0, __Ptr2Arr_len_" + varName + "_index)]";
                    }else {
                        replacement = "memory" + idStr + "[" + varName + "_index]";
                    }
                }

                TheRewriter.ReplaceText(DRE->getSourceRange(), replacement);
            }
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitStringLiteral(clang::StringLiteral *SL) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();

    if (!SM.isInMainFile(SL->getBeginLoc())) return true;

    std::string content = SL->getString().str();

    // Convert string literal to a pointer like "str_lit_0"
    for(const auto& pts : pointsToStrings) {
        if (pts.content == content + std::string("\0",1)) {
            // Check if the parent is a VarDecl with array type
            auto Parents = Context->getParents(*SL);
            if (!Parents.empty()) {
                if (const clang::VarDecl *VD = Parents[0].get<clang::VarDecl>()) {
                    if (VD->getType()->isArrayType()) {
                        return true;
                    }
                }
            }

            // Replace the string literal with the variable name
            TheRewriter.ReplaceText(SL->getSourceRange(), pts.varName);
            break;
        }
    }

    return true;
}

bool CodeVisitorAndRewriter::VisitMemberExpr(clang::MemberExpr *ME) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(ME->getBeginLoc())) {
        if (TheRewriter.isReplaced(ME->getSourceRange())) {
            return true;
        }
        if (ME->isArrow()) {
            //llvm::outs() << "Member Access" << "\n";
            clang::Expr *basePointer = ME->getBase()->IgnoreParenImpCasts();
            clang::SourceRange basePointerRange = basePointer->getSourceRange();
            std::string basePointerStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(basePointerRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

            std::string memberAccessed = ME->getMemberNameInfo().getAsString();

            bool isPointee = false;

            for (size_t i = 0; i < memorySets.size(); ++i) {
                ScopedPointer basePointerSp = {currentFunction, basePointerStr};
                if (std::find(memorySets[i].pointees.begin(), memorySets[i].pointees.end(), basePointerSp) != memorySets[i].pointees.end()) {
                    isPointee = true;
                    break;
                }
            }

            for (size_t i = 0; i < memorySets.size(); ++i) {
                ScopedPointer basePointerSp = {currentFunction, basePointerStr};
                if (std::find(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), basePointerSp) != memorySets[i].pointers.end()) {

                    std::string idx = isPointee ? (basePointerStr + "_index") : basePointerStr;
                    std::string idStr = std::to_string(i);
                    std::string textToReplace;

                    if (tracksBounds()) {
                        std::string safeIndex = "safe_idx_memory" + idStr + "(__Ptr2Arr_base_" + idx + "," + idx + ",0, __Ptr2Arr_len_" + idx + ")";
                        textToReplace = "memory" + idStr + "[" + safeIndex + "]." + memberAccessed;
                    }else {
                        textToReplace = "memory" + idStr + "[" + idx + "]." + memberAccessed;
                    }

                    TheRewriter.ReplaceText(ME->getSourceRange(), textToReplace);
                    break;
                }
            }
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitArraySubscriptExpr(clang::ArraySubscriptExpr *ASE) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(ASE->getBeginLoc())) {
        clang::Expr *expr = ASE->IgnoreParenImpCasts();
        clang::SourceRange exprRange = expr->getSourceRange();
        std::string exprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(exprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

        clang::SourceLocation lineStartLoc = SM.translateLineCol(SM.getFileID(ASE->getBeginLoc()), SM.getSpellingLineNumber(ASE->getBeginLoc()), 1);
        clang::SourceLocation lineEndLoc = lineStartLoc;
        while (SM.getCharacterData(lineEndLoc)[0] != '\n' && SM.getCharacterData(lineEndLoc)[0] != '\0') {
            lineEndLoc = lineEndLoc.getLocWithOffset(1);
        }
        std::string lineText = std::string(SM.getCharacterData(lineStartLoc), SM.getCharacterData(lineEndLoc) - SM.getCharacterData(lineStartLoc));

        std::string escapedExprStr;
        for (char c : exprStr) {
            if (c == '[' || c == ']') {
                escapedExprStr += '\\';
            }
            escapedExprStr += c;
        }
        std::regex pattern_deref("&\\s*\\(?\\s*" + escapedExprStr + "\\s*\\)?");
        std::regex pattern_land("&&\\s*\\(?\\s*" + escapedExprStr + "\\s*\\)?");

        if (std::regex_search(lineText, pattern_land) || !std::regex_search(lineText, pattern_deref)) {
            clang::Expr *baseExpr = ASE->getBase()->IgnoreParenImpCasts();
            clang::Expr *idxExpr = ASE->getIdx()->IgnoreParenImpCasts();
            std::string arrayName = TheRewriter.getRewrittenText(baseExpr->getSourceRange());
            std::string arrayIndex = TheRewriter.getRewrittenText(idxExpr->getSourceRange());

            for (size_t i = 0; i < memorySets.size(); ++i) {
                std::string idStr = std::to_string(i);

                if (std::find_if(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), [&arrayName](const ScopedPointer& s) { return s.pointerName == arrayName; }) != memorySets[i].pointers.end()) {
                    std::string indexStr = arrayName + " + (" + arrayIndex + ")";

                    if (memorySets[i].accessedTypes.size() > 1) {
                        if (tracksBounds()) {
                            std::string textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(ASE->getType()) + "(__Ptr2Arr_base_" + arrayName + "," + indexStr + ", __Ptr2Arr_len_" + arrayName + ")";
                            TheRewriter.ReplaceText(ASE->getSourceRange(), textToReplace);
                        } else {
                            std::string textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(ASE->getType()) + "(" + indexStr + ")";
                            TheRewriter.ReplaceText(ASE->getSourceRange(), textToReplace);
                        }
                    } else {
                        if (tracksBounds()) {
                            std::string entireToReplace = "memory" + idStr + "[safe_idx_memory" + idStr + "(__Ptr2Arr_base_" + arrayName + "," + arrayName + ", " + arrayIndex + ", __Ptr2Arr_len_" + arrayName + ")]";
                            TheRewriter.ReplaceText(ASE->getSourceRange(), entireToReplace);
                        }else {
                            std::string textToReplace = "memory" + idStr + "[" + indexStr + "]";
                            TheRewriter.ReplaceText(ASE->getSourceRange(), textToReplace);
                        }
                    }
                    break;
                }
                if (std::find_if(memorySets[i].pointees.begin(), memorySets[i].pointees.end(), [&arrayName](const ScopedPointer& s) { return s.pointerName == arrayName; }) != memorySets[i].pointees.end()) {
                    std::string indexStr = arrayName + "_index + (" + arrayIndex + ")";

                    if (memorySets[i].accessedTypes.size() > 1) {
                        if (tracksBounds()) {
                            std::string textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(ASE->getType()) + "(__Ptr2Arr_base_" + arrayName + "_index," + indexStr + ", __Ptr2Arr_len_" + arrayName + "_index)";
                            TheRewriter.ReplaceText(ASE->getSourceRange(), textToReplace);
                        } else {
                            std::string textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(ASE->getType()) + "(" + indexStr + ")";
                            TheRewriter.ReplaceText(ASE->getSourceRange(), textToReplace);
                        }
                    } else {
                        if (tracksBounds()) {
                            std::string entireToReplace = "memory" + idStr + "[safe_idx_memory" + idStr + "(__Ptr2Arr_base_" + arrayName + "_index," + arrayName + "_index, " + arrayIndex + ", __Ptr2Arr_len_" + arrayName + "_index)]";
                            TheRewriter.ReplaceText(ASE->getSourceRange(), entireToReplace);
                        }else {
                            std::string textToReplace = "memory" + idStr + "[" + indexStr + "]";
                            TheRewriter.ReplaceText(ASE->getSourceRange(), textToReplace);
                        }
                    }
                    break;
                }
            }
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitBinaryOperator(clang::BinaryOperator *BO) {
    if (isPreCheckPhase) return true;
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(BO->getBeginLoc())) {

        if (BO->isAssignmentOp()) {
            std::string rewrittenLHS = TheRewriter.getRewrittenText(BO->getLHS()->getSourceRange());

            // Regex to capture load_memoryX_type(index, ...)
            std::regex loadRegex("^\\s*\\(?\\s*load_memory(\\d+)_([a-zA-Z]+)\\(([^,)]*)(?:,\\s*([^,)]*)\\s*,\\s*([^,)]*)\\s*)?\\)\\s*\\)?\\s*$");
            std::smatch match;

            if (std::regex_match(rewrittenLHS, match, loadRegex)) {
                std::string id = match[1].str();
                std::string suffix = match[2].str();
                std::string indexStr = match[3].str();
                std::string rewrittenRHS = TheRewriter.getRewrittenText(BO->getRHS()->getSourceRange());
                std::string operatorStr = BO->getOpcodeStr().str();

                std::string replacement;
                // Under bounds tracking a load is `load_memoryN_T(base, index, len)` and a store takes
                // (base, index, value, len). Every parameter is an int, so arguments in another order
                // still compile, and the bounds test then reads the wrong values.
                std::string baseParam = match[4].matched ? match[3].str() : "__Ptr2Arr_base_" + indexStr;
                std::string indexParam = match[4].matched ? match[4].str() : indexStr;
                std::string lenParam = match[4].matched ? match[5].str() : "__Ptr2Arr_len_" + indexStr;
                if (operatorStr == "=") {
                    // Simple assignment
                    if (tracksBounds()) {
                        replacement = "store_memory" + id + "_" + suffix + "(" + baseParam + "," + indexParam + ", " + rewrittenRHS + ", " + lenParam + ")";
                    } else {
                        replacement = "store_memory" + id + "_" + suffix + "(" + indexStr + ", " + rewrittenRHS + ")";
                    }
                } else {
                    // Compound assignment (e.g., +=, -=): store(index, load(index) OP RHS)
                    char op = operatorStr[0];
                    if (tracksBounds()) {
                        replacement = "store_memory" + id + "_" + suffix + "(" + baseParam + "," + indexParam + ", load_memory" + id + "_" + suffix + "(" + baseParam + "," + indexParam + ", " + lenParam + ") " + op + " " + rewrittenRHS + ", " + lenParam + ")";
                    } else {
                        replacement = "store_memory" + id + "_" + suffix + "(" + indexStr + ", load_memory" + id + "_" + suffix + "(" + indexStr + ") " + op + " " + rewrittenRHS + ")";
                    }
                }

                // Replace the entire assignment expression with the store function call
                TheRewriter.ReplaceText(BO->getSourceRange(), replacement);
                return true;
            }
        }

        if (BO->getOpcode() == clang::BO_Assign) {
            std::string varName;
            if (auto *DRE = llvm::dyn_cast<clang::DeclRefExpr>(BO->getLHS()->IgnoreParenImpCasts())) {
                varName = DRE->getDecl()->getNameAsString();
            }

            int id;
            bool isPointer = false;
            for (int i = 0; i < memorySets.size(); ++i) {
                if (std::find_if(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), [&varName](const ScopedPointer& s) { return s.pointerName == varName; }) != memorySets[i].pointers.end()) {
                    id = i;
                    isPointer = true;
                    break;
                }
            }

            if (isPointer) {
                clang::Expr *initExpr = BO->getRHS()->IgnoreParenImpCasts();
                clang::SourceRange initExprRange = initExpr->getSourceRange();
                std::string initExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(initExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                // 💡 1. Check if the Right-Hand Side (RHS) is a NULL pointer constant
                bool isRhsNull = BO->getRHS()->isNullPointerConstant(*Context, clang::Expr::NPC_ValueDependentIsNull);

                if (isRhsNull)
                {
                    // 💡 2. Replace the RHS macro "NULL" with "0" safely using ExpansionLoc
                    clang::SourceLocation startLoc = SM.getExpansionLoc(BO->getRHS()->getBeginLoc());
                    clang::SourceLocation endLoc = SM.getExpansionLoc(BO->getRHS()->getEndLoc());
                    clang::CharSourceRange replaceRange = clang::CharSourceRange::getTokenRange(startLoc, endLoc);

                    if (tracksBounds()) {
                        std::string textToReplace = "0;\n    __Ptr2Arr_len_" + varName + " = 0;\n       __Ptr2Arr_base_" + varName + " = 0";
                        TheRewriter.ReplaceText(replaceRange, textToReplace);
                    } else {
                        TheRewriter.ReplaceText(replaceRange, "0");
                    }
                } else if(initExprStr.find("alloca") != std::string::npos) {
                    std::string size;
                    std::regex allocaPattern(".*alloca\\s*\\(\\s*(.*?)\\s*\\)");
                    std::smatch match;
                    if (std::regex_match(initExprStr, match, allocaPattern)) {
                        size = match[1].str();
                        size = modelSize(size, memorySets[id]);
                    }

                    std::string textToReplace;
                    if (tracksBounds()) {
                        textToReplace = varName + " = allocate_memory" + std::to_string(id) + "(" + size + ");\n"
                                        "    __Ptr2Arr_len_" + varName + " = " + size + ";\n"
                                        "    __Ptr2Arr_base_" + varName + " = " + varName;
                    } else {
                        textToReplace = varName + " = allocate_memory" + std::to_string(id) + "(" + size + ")";
                    }

                    auto &SMExp = TheRewriter.getSourceMgr();
                    TheRewriter.ReplaceText(
                        clang::CharSourceRange::getCharRange(
                            SMExp.getExpansionLoc(BO->getBeginLoc()),
                            clang::Lexer::getLocForEndOfToken(initExpr->getEndLoc(), 0, SMExp, TheRewriter.getLangOpts())),
                        textToReplace);
                } else if (initExprStr.find("malloc") != std::string::npos) {
                    std::string size;
                    std::regex mallocPattern(".*malloc\\s*\\(\\s*(.*?)\\s*\\)");
                    std::smatch match;
                    if (std::regex_match(initExprStr, match, mallocPattern)) {
                        size = match[1].str();
                        size = modelSize(size, memorySets[id]);
                    }

                    std::string textToReplace;
                    if (tracksBounds()) {
                        textToReplace = varName + " = allocate_memory" + std::to_string(id) + "(" + size + ");\n"
                                        "    __Ptr2Arr_len_" + varName + " = " + size + ";\n"
                                        "    __Ptr2Arr_base_" + varName + " = " + varName;
                    } else {
                        textToReplace = varName + " = allocate_memory" + std::to_string(id) + "(" + size + ")";
                    }

                    auto &SMExp = TheRewriter.getSourceMgr();
                    TheRewriter.ReplaceText(
                        clang::CharSourceRange::getCharRange(
                            SMExp.getExpansionLoc(BO->getBeginLoc()),
                            clang::Lexer::getLocForEndOfToken(initExpr->getEndLoc(), 0, SMExp, TheRewriter.getLangOpts())),
                        textToReplace);
                } else {
                    if (tracksBounds()) {
                        std::string rewrittenRHS = TheRewriter.getRewrittenText(BO->getRHS()->getSourceRange());
                        std::string textToReplace;
                        // The bounds of the block the value points into, which pointer arithmetic
                        // does not move: `p = q + 1` keeps q's base and length.
                        std::string len, base;
                        if (!boundsOf(BO->getRHS(), len, base)) unknownBounds(len, base);
                        if(len == "__Ptr2Arr_len_" + varName){
                            textToReplace = "(" + varName + " = " + rewrittenRHS + ")";
                        }else {
                            textToReplace = "(" + varName + " = " + rewrittenRHS + ","
                                                        "    __Ptr2Arr_len_" + varName + " = " + len + ","
                                                        "    __Ptr2Arr_base_" + varName + " = " + base + ")";
                        }
                        auto &SMExp = TheRewriter.getSourceMgr();
                        TheRewriter.ReplaceText(
                            clang::CharSourceRange::getTokenRange(
                                SMExp.getExpansionLoc(BO->getBeginLoc()),
                                SMExp.getExpansionLoc(BO->getEndLoc())),
                            textToReplace);
                    }
                }
            }
        }
    }
    return true;
}

std::string getBaseIdentifier(clang::Expr *E) {
    if (!E) return "";
    E = E->IgnoreParenImpCasts();

    if (auto *DRE = dyn_cast<clang::DeclRefExpr>(E)) {
        return DRE->getNameInfo().getAsString();
    }
    if (auto *UO = dyn_cast<clang::UnaryOperator>(E)) {
        return getBaseIdentifier(UO->getSubExpr());
    }
    if (auto *ASE = dyn_cast<clang::ArraySubscriptExpr>(E)) {
        return getBaseIdentifier(ASE->getBase());
    }
    if (auto *BO = dyn_cast<clang::BinaryOperator>(E)) {
        if (BO->getLHS()->getType()->isPointerType() || BO->getLHS()->getType()->isArrayType())
            return getBaseIdentifier(BO->getLHS());
        if (BO->getRHS()->getType()->isPointerType() || BO->getRHS()->getType()->isArrayType())
            return getBaseIdentifier(BO->getRHS());
    }
    return "";
}

int getSetIndexByPointer(const ScopedPointer& targetPointer, const std::vector<MemorySet>& memorySets) {
    for (int i = 0; i < memorySets.size(); ++i) {
        auto& ps = memorySets[i].pointers;
        if (std::find(ps.begin(), ps.end(), targetPointer) != ps.end()) return i;
    }
    return -1;
}

int getNextSetIndex(int currentSetIndex, const std::vector<MemorySet>& memorySets) {
    if (currentSetIndex < 0 || currentSetIndex >= memorySets.size()) return -1;
    if (memorySets[currentSetIndex].pointees.empty()) return -1;
    ScopedPointer firstPointee = memorySets[currentSetIndex].pointees[0];

    return getSetIndexByPointer(firstPointee, memorySets);
}

bool CodeVisitorAndRewriter::VisitUnaryOperator(clang::UnaryOperator *UO) {
    if (isPreCheckPhase) return true;
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (SM.isInMainFile(UO->getBeginLoc())) {
        if (UO->getOpcode() == clang::UO_Deref) {
            auto parents = Context->getParents(*UO);
            if (!parents.empty()) {
                if (const auto *sizeofExpr = parents[0].get<clang::UnaryExprOrTypeTraitExpr>()) {
                    return true;
                }
            }

            clang::Expr *subExpr = UO->getSubExpr()->IgnoreParenImpCasts();

            std::string baseVar = getBaseIdentifier(UO->getSubExpr());
            int derefLevel = 0;
            clang::Expr* tempExpr = UO->getSubExpr()->IgnoreParenImpCasts();
            while (auto* subUO = dyn_cast<clang::UnaryOperator>(tempExpr)) {
                if (subUO->getOpcode() == clang::UO_Deref) {
                    derefLevel++;
                    tempExpr = subUO->getSubExpr()->IgnoreParenImpCasts();
                } else {
                    break;
                }
            }

            int currentSetID = getSetIndexByPointer(ScopedPointer{currentFunction, baseVar}, memorySets);
            for (int i = 0; i < derefLevel; ++i) {
                currentSetID = getNextSetIndex(currentSetID, memorySets);
            }

            if (auto *DRE = dyn_cast<clang::DeclRefExpr>(subExpr)) {
                std::string varName = DRE->getNameInfo().getAsString();

                for (size_t i = 0; i < memorySets.size(); ++i) {
                    std::string idStr = std::to_string(i);
                    if (std::find_if(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), [&varName](const ScopedPointer& s) { return s.pointerName == varName; }) != memorySets[i].pointers.end()) {
                        bool handled = false;
                        for (size_t j = 0; j < memorySets.size(); ++j)
                        {
                            if (std::find_if(memorySets[j].pointees.begin(), memorySets[j].pointees.end(), [&varName](const ScopedPointer &s) { return s.pointerName == varName; }) != memorySets[j].pointees.end())
                            {
                                std::string innerIndex = "memory" + std::to_string(j) + "[" + varName + "_index]";
                                std::string textToReplace;

                                if (memorySets[i].accessedTypes.size() > 1) {
                                    if (tracksBounds()) {
                                        textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(UO->getType()) + "(__Ptr2Arr_base_" + varName + ","  + innerIndex + ", __Ptr2Arr_len_" + varName + "_index)";
                                    } else {
                                        textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(UO->getType()) + "(" + innerIndex + ")";
                                    }
                                } else {
                                    if (tracksBounds()) {
                                        textToReplace = "memory" + idStr + "[safe_idx_memory" + idStr + "( __Ptr2Arr_base_" + varName + "_index," + innerIndex + ",0, __Ptr2Arr_len_" + varName + "_index)]";
                                    }else {
                                        textToReplace = "memory" + idStr + "[" + innerIndex + "]";
                                    }
                                }
                                TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
                                handled = true;
                                return true;
                            }
                        }
                        if (!handled) {
                            std::string textToReplace;
                            if (memorySets[i].accessedTypes.size() > 1) {
                                if (tracksBounds()) {
                                    textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(UO->getType()) + "(__Ptr2Arr_base_" + varName + "," + varName + ", __Ptr2Arr_len_" + varName + ")";
                                } else {
                                    textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(UO->getType()) + "(" + varName + ")";
                                }
                            } else {
                                if (tracksBounds()) {
                                    textToReplace = "memory" + idStr + "[safe_idx_memory" + idStr + "(__Ptr2Arr_base_" + varName + "," + varName +",0, __Ptr2Arr_len_" + varName + ")]";
                                }else {
                                    textToReplace = "memory" + idStr + "[" + varName + "]";
                                }
                            }
                            TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
                            break;
                        }
                    }
                }
            }

            else if (auto *unaryOp = dyn_cast<clang::UnaryOperator>(subExpr)) {
                if (currentSetID != -1 && memorySets[currentSetID].accessedTypes.size() > 1) {
                    if (tracksBounds() && !baseVar.empty()) {
                        TheRewriter.ReplaceText(UO->getOperatorLoc(), 1, "load_memory" + std::to_string(currentSetID) + "_" + getTypeSuffix(UO->getType()) + "(__Ptr2Arr_base_" + baseVar + ",");
                        TheRewriter.InsertTextAfterToken(UO->getEndLoc(), ", __Ptr2Arr_len_" + baseVar + ")");
                    } else {
                        TheRewriter.ReplaceText(UO->getOperatorLoc(), 1, "load_memory" + std::to_string(currentSetID) + "_" + getTypeSuffix(UO->getType()) + "(");
                        TheRewriter.InsertTextAfterToken(UO->getEndLoc(), ")");
                    }
                } else {
                    std::string idStr = std::to_string(currentSetID);
                    if (tracksBounds()) {
                        std::string lenParam = !baseVar.empty() ? "__Ptr2Arr_len_" + baseVar : "0";
                        std::string baseParam = !baseVar.empty() ? "__Ptr2Arr_base_" + baseVar : "0";
                        TheRewriter.ReplaceText(UO->getOperatorLoc(), 1, "memory" + idStr + "[safe_idx_memory" + idStr + "(" + baseParam + ",");
                        TheRewriter.InsertTextAfterToken(UO->getEndLoc(), ", 0, " + lenParam + ")]");
                    }else {
                        TheRewriter.ReplaceText(UO->getOperatorLoc(), 1, "memory" + idStr + "[");
                        TheRewriter.InsertTextAfterToken(UO->getEndLoc(), "]");
                    }
                }
            }

            else if (auto *binaryOp1 = dyn_cast<clang::BinaryOperator>(subExpr)) {
                clang::Expr *basePointer1 = binaryOp1->getLHS()->IgnoreParenImpCasts();

                if (auto *binaryOp2 = dyn_cast<clang::BinaryOperator>(basePointer1)) {
                    clang::Expr *basePointer2 = binaryOp2->getLHS()->IgnoreParenImpCasts();
                    clang::SourceRange basePointerRange = basePointer2->getSourceRange();
                    std::string basePointerStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(basePointerRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                    for (size_t i = 0; i < memorySets.size(); ++i) {
                        if (std::find_if(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), [&basePointerStr](const ScopedPointer& s) { return s.pointerName == basePointerStr; }) != memorySets[i].pointers.end()) {
                            clang::SourceRange subExprRange = subExpr->getSourceRange();
                            std::string subExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(subExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                            std::string textToReplace;
                            std::string idStr = std::to_string(i);
                            if (memorySets[i].accessedTypes.size() > 1) {
                                if (tracksBounds()) {
                                    textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(UO->getType()) + "(__Ptr2Arr_base_" + basePointerStr + "," + subExprStr + ", __Ptr2Arr_len_" + basePointerStr + ")";
                                } else {
                                    textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(UO->getType()) + "(" + subExprStr + ")";
                                }
                            } else {
                                if (tracksBounds()) {
                                    textToReplace = "memory" + idStr + "[safe_idx_memory" + idStr + "(__Ptr2Arr_base_" + basePointerStr + "," + subExprStr + ",0, __Ptr2Arr_len_" + basePointerStr + ")]";
                                }else {
                                    textToReplace = "memory" + idStr + "[" + subExprStr + "]";
                                }
                            }
                            TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
                            break;
                        }
                    }
                }

                else {
                    clang::SourceRange basePointerRange = basePointer1->getSourceRange();
                    std::string basePointerStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(basePointerRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                    for (size_t i = 0; i < memorySets.size(); ++i) {
                        if (std::find_if(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), [&basePointerStr](const ScopedPointer& s) { return s.pointerName == basePointerStr; }) != memorySets[i].pointers.end()) {
                            clang::SourceRange subExprRange = subExpr->getSourceRange();
                            std::string subExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(subExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                            std::string textToReplace;
                            std::string idStr = std::to_string(i);
                            if (tracksBounds()) {
                                textToReplace = "memory" + idStr + "[safe_idx_memory" + idStr + "(__Ptr2Arr_base_" + basePointerStr + "," + subExprStr + ",0, __Ptr2Arr_len_" + basePointerStr + ")]";
                            }else {
                                textToReplace = "memory" + idStr + "[" + subExprStr + "]";
                            }
                            TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
                            break;
                        }
                    }
                }
            }

            else if (auto *CE = dyn_cast<clang::CStyleCastExpr>(subExpr)) {
                clang::Expr *basePointer1 = CE->getSubExpr()->IgnoreImpCasts();

                if (auto *unaryOp = dyn_cast<clang::UnaryOperator>(basePointer1)) {
                    clang::Expr *basePointer2 = unaryOp->getSubExpr()->IgnoreParenImpCasts();
                    clang::SourceRange basePointerRange = basePointer2->getSourceRange();
                    std::string basePointerStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(basePointerRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                    for (size_t i = 0; i < memorySets.size(); ++i) {
                        if (std::find_if(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), [&basePointerStr](const ScopedPointer& s) { return s.pointerName == basePointerStr; }) != memorySets[i].pointers.end()) {
                            clang::SourceRange subExprRange = unaryOp->getSourceRange();
                            std::string subExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(subExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                            std::string textToReplace;
                            std::string idStr = std::to_string(i);
                            if (memorySets[i].accessedTypes.size() > 1) {
                                if (tracksBounds()) {
                                    textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(UO->getType()) + "(__Ptr2Arr_base_" + basePointerStr + "," + subExprStr + ", __Ptr2Arr_len_" + basePointerStr + ")";
                                } else {
                                    textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(UO->getType()) + "(" + subExprStr + ")";
                                }
                            } else {
                                if (tracksBounds()) {
                                    textToReplace = "memory" + idStr + "[safe_idx_memory" + idStr + "( __Ptr2Arr_base_" + basePointerStr + "," + subExprStr + ",0, __Ptr2Arr_len_" + basePointerStr + ")]";
                                }else {
                                    textToReplace = "memory" + idStr + "[" + subExprStr + "]";
                                }
                            }
                            TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
                            break;
                        }
                    }
                }

                else {
                    clang::SourceRange basePointerRange = basePointer1->getSourceRange();
                    std::string basePointerStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(basePointerRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

                    for (size_t i = 0; i < memorySets.size(); ++i) {
                        if (std::find_if(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), [&basePointerStr](const ScopedPointer& s) { return s.pointerName == basePointerStr; }) != memorySets[i].pointers.end()) {
                            std::string textToReplace;
                            std::string idStr = std::to_string(i);
                            if (memorySets[i].accessedTypes.size() > 1) {
                                if (tracksBounds()) {
                                    textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(UO->getType()) + "(__Ptr2Arr_base_" + basePointerStr + "," + basePointerStr + ", __Ptr2Arr_len_" + basePointerStr + ")";
                                } else {
                                    textToReplace = "load_memory" + idStr + "_" + getTypeSuffix(UO->getType()) + "(" + basePointerStr + ")";
                                }
                            } else {
                                if (tracksBounds()) {
                                    textToReplace = "memory" + idStr + "[safe_idx_memory" + idStr + "(__Ptr2Arr_base_" + basePointerStr + "," + basePointerStr + ", 0, __Ptr2Arr_len_" + basePointerStr + ")]";
                                }else {
                                    textToReplace = "memory" + idStr + "[" + basePointerStr + "]";
                                }
                            }
                            TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
                            break;
                        }
                    }
                }
            }

            else if (auto *CallE = dyn_cast<clang::CallExpr>(subExpr))
            {
                if (clang::FunctionDecl *FD = CallE->getDirectCallee())
                {
                    std::string funcName = FD->getNameAsString();

                    if (functionReturnMap.count(funcName) && !functionReturnMap.at(funcName).empty())
                    {
                        int targetSetID = -1;
                        bool hasNull = false;
                        std::string originVarName = "";

                        for (const std::string &originVar : functionReturnMap.at(funcName))
                        {
                            if (originVar == "alloca" || originVar == "malloc")
                                continue;

                            if (originVar == "null"){
                                hasNull = true;
                                continue;
                            }

                            ScopedPointer targetSp = {funcName, originVar};

                            for (size_t i = 0; i < memorySets.size(); ++i)
                            {
                                if (std::find(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), targetSp) != memorySets[i].pointers.end())
                                {
                                    targetSetID = i;
                                    originVarName = originVar;
                                    break;
                                }
                            }
                            if (targetSetID != -1) break;
                        }

                        if (targetSetID != -1)
                        {
                            clang::SourceRange subExprRange = subExpr->getSourceRange();
                            std::string subExprStr = clang::Lexer::getSourceText(
                                clang::CharSourceRange::getTokenRange(subExprRange),
                                TheRewriter.getSourceMgr(),
                                TheRewriter.getLangOpts()).str();

                            std::string textToReplace;
                            std::string targetStr = std::to_string(targetSetID);

                            std::string lenParam = !originVarName.empty() ? "__Ptr2Arr_len_" + originVarName : "0";
                            std::string baseParam = !originVarName.empty() ? "__Ptr2Arr_base_" + originVarName : "0";

                            if (memorySets[targetSetID].accessedTypes.size() > 1) {
                                if (tracksBounds()) {
                                    textToReplace = "load_memory" + targetStr + "_" + getTypeSuffix(UO->getType()) + "("  + baseParam + "," + subExprStr + ", " + lenParam + ")";
                                } else {
                                    textToReplace = "load_memory" + targetStr + "_" + getTypeSuffix(UO->getType()) + "(" + subExprStr + ")";
                                }
                            } else {
                                if (tracksBounds()) {
                                    textToReplace = "memory" + targetStr + "[safe_idx_memory" + targetStr + "(" + baseParam + "," + subExprStr + ",0, " + lenParam + ")]";
                                }else {
                                    textToReplace = "memory" + targetStr + "[" + subExprStr + "]";
                                }
                            }
                            TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
                        } else if (hasNull) {
                            clang::SourceRange subExprRange = subExpr->getSourceRange();
                            std::string subExprStr = clang::Lexer::getSourceText(
                                clang::CharSourceRange::getTokenRange(subExprRange),
                                TheRewriter.getSourceMgr(),
                                TheRewriter.getLangOpts()).str();

                            std::string textToReplace;

                            if (tracksBounds()) {
                                textToReplace = "memory0[safe_idx_memory0(0," + subExprStr + ",  0, 0)]";
                            }else {
                                textToReplace = "memory0[" + subExprStr + "]";
                            }
                            TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
                        }
                    }
                }
            }
        }

        else if (UO->getOpcode() == clang::UO_AddrOf) {
            clang::Expr *subExpr = UO->getSubExpr()->IgnoreParenImpCasts();
            clang::SourceRange subExprRange = subExpr->getSourceRange();
            std::string subExprStr = clang::Lexer::getSourceText(clang::CharSourceRange::getTokenRange(subExprRange), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts()).str();

            if (isa<clang::DeclRefExpr>(subExpr)) {
                std::string textToReplace = subExprStr + "_index";
                TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
            }

            else if (isa<clang::ArraySubscriptExpr>(subExpr)) {
                size_t startBracket = subExprStr.find('[');
                size_t endBracket = subExprStr.find(']', startBracket);
                std::string arrayName = subExprStr.substr(0, startBracket);
                std::string arrayIndex = subExprStr.substr(startBracket + 1, endBracket - startBracket - 1);

                for (size_t i = 0; i < memorySets.size(); ++i) {
                    if (std::find_if(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), [&arrayName](const ScopedPointer& s) { return s.pointerName == arrayName; }) != memorySets[i].pointers.end()) {
                        std::string textToReplace = arrayName + " + " + arrayIndex;
                        TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
                        break;
                    }
                    if (std::find_if(memorySets[i].pointees.begin(), memorySets[i].pointees.end(), [&arrayName](const ScopedPointer& s) { return s.pointerName == arrayName; }) != memorySets[i].pointees.end()) {
                        std::string textToReplace = arrayName + "_index + " + arrayIndex;
                        TheRewriter.ReplaceText(UO->getSourceRange(), textToReplace);
                        break;
                    }
                }
            }
        }

        else if (UO->isIncrementDecrementOp()) {
            clang::Expr *subExpr = UO->getSubExpr()->IgnoreParenCasts();
            if (!subExpr) {
                return true;
            }

            bool isDereference = false;
            clang::Expr *pointerExpr = nullptr;
            std::string alreadyLoadedFuncName = "";

            if (auto *unaryDeref = clang::dyn_cast<clang::UnaryOperator>(subExpr)) {
                if (unaryDeref->getOpcode() == clang::UO_Deref) {
                    isDereference = true;
                    pointerExpr = unaryDeref->getSubExpr()->IgnoreParenCasts();
                }
            } else if (auto *callExpr = clang::dyn_cast<clang::CallExpr>(subExpr)) {
                if (auto *calleeDecl = clang::dyn_cast_or_null<clang::FunctionDecl>(callExpr->getCalleeDecl())) {
                    std::string calleeName = calleeDecl->getNameAsString();
                    if (calleeName.find("load_memory") != std::string::npos) {
                        isDereference = true;
                        alreadyLoadedFuncName = calleeName;
                        if (callExpr->getNumArgs() > 0) {
                            pointerExpr = callExpr->getArg(0)->IgnoreParenCasts();
                        }
                    }
                }
            }

            if (isDereference && pointerExpr) {
                clang::QualType qualType = subExpr->getType();
                std::string baseType = qualType.getAsString();

                if (qualType->isPointerType()) {
                    baseType = "int";
                }

                if (!alreadyLoadedFuncName.empty()) {
                    if (alreadyLoadedFuncName.find("_int") != std::string::npos) baseType = "int";
                    else if (alreadyLoadedFuncName.find("_char") != std::string::npos) baseType = "char";
                }

                if (baseType == "int" || baseType == "char") {
                    int memoryIndex = -1;
                    std::string detectedVarName = "";

                    if (!alreadyLoadedFuncName.empty()) {
                        size_t startPos = alreadyLoadedFuncName.find("memory") + 6;
                        size_t endPos = alreadyLoadedFuncName.find("_", startPos);
                        if (endPos != std::string::npos) {
                            memoryIndex = std::stoi(alreadyLoadedFuncName.substr(startPos, endPos - startPos));
                        }
                    } else {
                        std::string varName = "";
                        std::string funcScope = "";

                        clang::DynTypedNode node = clang::DynTypedNode::create(*UO);
                        while (true) {
                            auto parents = Context->getParents(node);
                            if (parents.empty()) break;
                            if (const auto *FD = parents[0].get<clang::FunctionDecl>()) {
                                funcScope = FD->getNameAsString();
                                break;
                            }
                            node = parents[0];
                        }

                        if (const auto *DRE = clang::dyn_cast<clang::DeclRefExpr>(pointerExpr)) {
                            varName = DRE->getNameInfo().getName().getAsString();
                        } else if (const auto *ME = clang::dyn_cast<clang::MemberExpr>(pointerExpr)) {
                            varName = ME->getMemberDecl()->getNameAsString();
                        }

                        if (!varName.empty() && !funcScope.empty()) {
                            detectedVarName = varName;
                            ScopedPointer targetSp = {funcScope, varName};

                            for (size_t midx = 0; midx < memorySets.size(); ++midx) {
                                if (std::find(memorySets[midx].pointers.begin(), memorySets[midx].pointers.end(), targetSp) != memorySets[midx].pointers.end()) {
                                    memoryIndex = static_cast<int>(midx);
                                    break;
                                }
                            }
                        }
                    }

                    if (memoryIndex == -1) {
                        return true;
                    }

                    bool generatesHelpers = (memorySets[memoryIndex].dataType == "unsigned char" &&
                                             memorySets[memoryIndex].accessedTypes.size() > 1);

                    if (!generatesHelpers) {
                        return true;
                    }

                    std::string funcName = "";
                    bool isPreOp = false;

                    if (UO->getOpcode() == clang::UO_PostDec || UO->getOpcode() == clang::UO_PreDec) {
                        requiredDecrementHelpers.insert({baseType, memoryIndex});
                        funcName = "post_decrement_memory" + std::to_string(memoryIndex) + "_" + baseType;

                        if (UO->getOpcode() == clang::UO_PreDec) {
                            isPreOp = true;
                        }
                    }
                    else if (UO->getOpcode() == clang::UO_PostInc || UO->getOpcode() == clang::UO_PreInc) {
                        requiredIncrementHelpers.insert({baseType, memoryIndex});
                        funcName = "post_increment_memory" + std::to_string(memoryIndex) + "_" + baseType;

                        if (UO->getOpcode() == clang::UO_PreInc) {
                            isPreOp = true;
                        }
                    }

                    if (!funcName.empty()) {
                        clang::SourceLocation startLoc = pointerExpr->getBeginLoc();
                        clang::SourceLocation endLoc = pointerExpr->getEndLoc();
                        if (startLoc.isValid() && endLoc.isValid()) {
                            std::string argumentStr = clang::Lexer::getSourceText(
                                clang::CharSourceRange::getTokenRange(startLoc, endLoc),
                                TheRewriter.getSourceMgr(),
                                Context->getLangOpts()
                            ).str();

                            if (!argumentStr.empty()) {
                                std::string replacement;
                                if (tracksBounds() && !detectedVarName.empty()) {
                                    // The helpers take (base, index, len), as `safe_idx_memoryN` does. Every
                                    // parameter is an int, so another order still compiles, and the bounds
                                    // test then reads the wrong values.
                                    std::string args = "__Ptr2Arr_base_" + detectedVarName + ", " + argumentStr + ", __Ptr2Arr_len_" + detectedVarName;
                                    if (isPreOp) {
                                        if (UO->getOpcode() == clang::UO_PreDec) {
                                            replacement = "(" + funcName + "(" + args + ") - 1)";
                                        } else {
                                            replacement = "(" + funcName + "(" + args + ") + 1)";
                                        }
                                    } else {
                                        replacement = funcName + "(" + args + ")";
                                    }
                                } else {
                                    if (isPreOp) {
                                        if (UO->getOpcode() == clang::UO_PreDec) {
                                            replacement = "(" + funcName + "(" + argumentStr + ") - 1)";
                                        } else {
                                            replacement = "(" + funcName + "(" + argumentStr + ") + 1)";
                                        }
                                    } else {
                                        replacement = funcName + "(" + argumentStr + ")";
                                    }
                                }
                                TheRewriter.ReplaceText(UO->getSourceRange(), replacement);
                            }
                        }
                    }
                }
            }
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::VisitCStyleCastExpr(clang::CStyleCastExpr *CE) {
    auto &SM = TheRewriter.getSourceMgr();

    clang::SourceLocation SpBegin = SM.getSpellingLoc(CE->getBeginLoc());
    if (!SM.isInMainFile(SpBegin)) return true;

    if (!CE->getTypeAsWritten()->isPointerType()) return true;

    llvm::StringRef buf = SM.getBufferData(SM.getFileID(SpBegin));
    size_t off = SM.getFileOffset(SpBegin);
    size_t start = buf.rfind('\n', off);
    start = (start == llvm::StringRef::npos) ? 0 : start + 1;
    size_t end = buf.find('\n', off);
    end = (end == llvm::StringRef::npos) ? buf.size() : end;
    std::string lineText = buf.substr(start, end - start).str();

    clang::SourceRange castExprRange = CE->IgnoreImpCasts()->getSourceRange();
    std::string castExprStr = clang::Lexer::getSourceText(
        clang::CharSourceRange::getTokenRange(SM.getExpansionLoc(castExprRange.getBegin()), SM.getExpansionLoc(castExprRange.getEnd())), SM, TheRewriter.getLangOpts()).str();

    if (lineText.find("alloca") != std::string::npos) return true;
    if (lineText.find("malloc") != std::string::npos) return true;
    if (lineText.find("*" + castExprStr) != std::string::npos) return true;

    clang::Expr *subExpr = CE->getSubExpr()->IgnoreImpCasts();
    clang::SourceLocation L = SM.getExpansionLoc(CE->getLParenLoc());
    clang::SourceLocation R = SM.getExpansionLoc(subExpr->getBeginLoc());
    if (!L.isValid() || !R.isValid()) return true;
    if (SM.getFileID(L) != SM.getFileID(R)) return true;
    if (SM.isBeforeInTranslationUnit(R, L)) return true;

    TheRewriter.RemoveText(clang::CharSourceRange::getCharRange(L, R));
    return true;
}

bool CodeVisitorAndRewriter::VisitUnaryExprOrTypeTraitExpr(clang::UnaryExprOrTypeTraitExpr *UE) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    if (!SM.isInMainFile(UE->getBeginLoc())) {
        return true;
    }

    if (UE->getKind() != clang::UETT_SizeOf) {
        return true;
    }

    // Get the source text to check if it contains pointer/array variables
    std::string sizeofText = clang::Lexer::getSourceText(
        clang::CharSourceRange::getTokenRange(UE->getSourceRange()),
        SM, Context->getLangOpts()).str();

    // Check if it contains array/pointer variables
    bool containsPointee = false;
    std::string foundPointee;
    for (const auto &memSet : memorySets) {
        for (const auto &pointee : memSet.pointees) {
            if (sizeofText.find(pointee.pointerName) != std::string::npos) {
                containsPointee = true;
                foundPointee = pointee.pointerName;
                break;
            }
        }
        if (containsPointee) break;
    }

    if (!containsPointee) {
        return true;  // No pointer/array variables, leave as is
    }

    // Handle different sizeof patterns
    if (!UE->isArgumentType()) {
        clang::Expr *arg = UE->getArgumentExpr()->IgnoreParenImpCasts();

        // Pattern 1: sizeof(*ptr) → sizeof(element_type)
        if (auto *deref = dyn_cast<clang::UnaryOperator>(arg)) {
            if (deref->getOpcode() == clang::UO_Deref) {
                clang::QualType pointeeType = deref->getType();
                std::string typeStr = pointeeType.getAsString();

                std::string replacement = "sizeof(int)";
                if (typeStr.find("char") != std::string::npos) {
                    replacement = "sizeof(char)";
                } else if (typeStr.find("float") != std::string::npos) {
                    replacement = "sizeof(float)";
                } else if (typeStr.find("double") != std::string::npos) {
                    replacement = "sizeof(double)";
                }

                TheRewriter.ReplaceText(UE->getSourceRange(), replacement);
                return true;
            }
        }

        // Pattern 2: sizeof(arr) → array_size * sizeof(element_type)
        if (auto *DRE = dyn_cast<clang::DeclRefExpr>(arg)) {
            if (auto *VD = dyn_cast<clang::VarDecl>(DRE->getDecl())) {
                std::string varName = VD->getNameAsString();

                // Check if this is an array with known size
                if (arrayVariableSizes.count(varName)) {
                    std::string arraySize = arrayVariableSizes[varName];
                    clang::QualType varType = VD->getType();

                    // Get element type
                    std::string elementType = "int";
                    if (const auto *arrType = dyn_cast<clang::ConstantArrayType>(varType.getTypePtr())) {
                        clang::QualType elemType = arrType->getElementType();
                        std::string elemTypeStr = elemType.getAsString();
                        if (elemTypeStr.find("char") != std::string::npos) {
                            elementType = "char";
                        } else if (elemTypeStr.find("float") != std::string::npos) {
                            elementType = "float";
                        } else if (elemTypeStr.find("double") != std::string::npos) {
                            elementType = "double";
                        }
                    }

                    std::string replacement = "(" + arraySize + " * sizeof(" + elementType + "))";
                    TheRewriter.ReplaceText(UE->getSourceRange(), replacement);
                    return true;
                }
            }
        }
    }

    return true;
}

bool CodeVisitorAndRewriter::VisitCallExpr(clang::CallExpr *CE) {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();

    if (!SM.isInMainFile(CE->getBeginLoc())) {
        return true;
    }

    if (const auto *FD = CE->getDirectCallee()) {
        std::string funcName = FD->getNameAsString();

        if (isPreCheckPhase) {
            if (funcName == "free") {
                hasFreeInCode = true;
            }
            return true;
        }

        if (!tracksBounds()) {
            return true;
        }

        if (TheRewriter.isReplaced(CE->getSourceRange())) {
            return true;
        }

        if (funcName == "free") {
            if (AssumeSafety) {
                // A free is a no-op under --assume-safety. `allocate_memoryN` never hands out an
                // index twice, so a block left in place changes no execution that does not touch
                // it after the free, which every memory-safe execution is; an invalid free or a
                // use after free is the --memory-safety program's to catch. An argument other than
                // a plain variable is still evaluated, since evaluating it can read through a
                // pointer (`free(p->next)`), which the assumption may cut off.
                std::string replacement = "(void)0";
                if (CE->getNumArgs() > 0 && !llvm::isa<clang::DeclRefExpr>(CE->getArg(0)->IgnoreParenImpCasts())) {
                    std::string argText = TheRewriter.getRewrittenText(CE->getArg(0)->getSourceRange());
                    if (!argText.empty()) {
                        replacement = "(void)(" + argText + ")";
                    }
                }
                TheRewriter.ReplaceText(CE->getSourceRange(), replacement);
                WriteToFile("FreeRewrite, " + currentFunction + ", noop_free");
            } else if (CE->getNumArgs() > 0) {
                clang::Expr *arg = CE->getArg(0)->IgnoreImpCasts();

                clang::SourceLocation argBegin = arg->getBeginLoc();
                clang::SourceLocation argEnd = arg->getEndLoc();
                std::string argStr = clang::Lexer::getSourceText(
                    clang::CharSourceRange::getTokenRange(argBegin, argEnd),
                    SM, TheRewriter.getLangOpts()).str();

                int id = -1;
                std::string varName = "";
                if (const auto *DRE = llvm::dyn_cast<clang::DeclRefExpr>(arg)) {
                    if (const auto *VD = llvm::dyn_cast<clang::VarDecl>(DRE->getDecl())) {
                        varName = VD->getNameAsString();
                        ScopedPointer varSp = {currentFunction, varName};

                        for (size_t i = 0; i < memorySets.size(); ++i) {
                            if (std::find(memorySets[i].pointers.begin(), memorySets[i].pointers.end(), varSp) != memorySets[i].pointers.end() ||
                                std::find(memorySets[i].pointees.begin(), memorySets[i].pointees.end(), varSp) != memorySets[i].pointees.end()) {
                                id = i;
                                break;
                            }
                        }
                    }
                }

                if (id != -1) {
                    std::string replacement;
                    std::string memIdx = std::to_string(id);

                    if (!varName.empty()) {
                        replacement = "free_memory" + memIdx + "(__Ptr2Arr_base_" + varName + "," + varName +", __Ptr2Arr_len_" + varName + ")";
                    } else {
                        replacement = "free_memory" + memIdx + "(" + argStr + ", 0)";
                    }
                    TheRewriter.ReplaceText(CE->getSourceRange(), replacement);
                    WriteToFile("FreeRewrite, " + currentFunction + ", free_memory" + memIdx);
                }
            }
        }
        else if (FD->hasBody()) {
            std::string exprSync = "";
            unsigned numArgs = CE->getNumArgs();
            unsigned numParams = FD->getNumParams();

            for (unsigned i = 0; i < numArgs && i < numParams; ++i) {
                const clang::ParmVarDecl *param = FD->getParamDecl(i);
                clang::Expr *arg = CE->getArg(i)->IgnoreParenImpCasts();

                if (param->getType()->isPointerType() || param->getType()->isArrayType()) {
                    std::string paramName = param->getNameAsString();
                    // A call's result as the argument: its bounds exist only once that call has
                    // returned, so the argument itself takes them over, `g(f())` becoming
                    // `g((__Ptr2Arr_ret_val_f = f(), __Ptr2Arr_len_p = __Ptr2Arr_ret_len_f, …,
                    // __Ptr2Arr_ret_val_f))`. Each argument does so right after its own call, so
                    // `g(f(), f())` gives each parameter its own call's bounds.
                    const auto *argCall = llvm::dyn_cast<clang::CallExpr>(arg->IgnoreParenCasts());
                    std::string returned = argCall ? trackedReturnName(argCall) : "";
                    if (!returned.empty() && !paramName.empty() && !isPreCheckPhase) {
                        clang::SourceRange argRange = CE->getArg(i)->getSourceRange();
                        std::string argText = TheRewriter.getRewrittenText(argRange);
                        if (!argText.empty()) {
                            std::string wrapped = "(__Ptr2Arr_ret_val_" + returned + " = " + argText +
                                                  ", __Ptr2Arr_len_" + paramName + " = __Ptr2Arr_ret_len_" + returned +
                                                  ", __Ptr2Arr_base_" + paramName + " = __Ptr2Arr_ret_base_" + returned +
                                                  ", __Ptr2Arr_ret_val_" + returned + ")";
                            if (!TheRewriter.ReplaceText(argRange, wrapped)) continue;
                            llvm::errs() << "[Ptr2Arr] Warning: the bounds of an argument of " << funcName << " could not be passed\n";
                        }
                    }

                    // The bounds of the block the argument points into: `f(b + 1)` passes b's, and a
                    // null pointer passes no block.
                    std::string argName = boundsOwner(arg, memorySets);
                    if (argName.empty() && !paramName.empty() &&
                        arg->isNullPointerConstant(*Context, clang::Expr::NPC_ValueDependentIsNull)) {
                        exprSync += "__Ptr2Arr_len_" + paramName + " = 0, ";
                        exprSync += "__Ptr2Arr_base_" + paramName + " = 0, ";
                        continue;
                    }

                    if (!argName.empty() && !paramName.empty()) {
                        exprSync += "__Ptr2Arr_len_" + paramName + " = __Ptr2Arr_len_" + argName + ", ";
                        exprSync += "__Ptr2Arr_base_" + paramName + " = __Ptr2Arr_base_" + argName + ", ";
                    } else if (!paramName.empty()) {
                        // Bounds that cannot be found must not decide anything. Under --memory-safety
                        // a length of 0 reports every access through the parameter (a null argument
                        // is one); under --assume-safety the whole memory array cuts none. Leaving the
                        // parameter's previous bounds, as before, could do either.
                        int setId = -1;
                        ScopedPointer paramSp = {FD->getNameAsString(), paramName};
                        for (size_t k = 0; k < memorySets.size(); ++k) {
                            if (std::find(memorySets[k].pointers.begin(), memorySets[k].pointers.end(), paramSp) != memorySets[k].pointers.end()) {
                                setId = k;
                                break;
                            }
                        }
                        if (setId != -1) {
                            std::string len = AssumeSafety ? "MEMORY" + std::to_string(setId) + "_SIZE" : "0";
                            exprSync += "__Ptr2Arr_len_" + paramName + " = " + len + ", ";
                            exprSync += "__Ptr2Arr_base_" + paramName + " = 0, ";
                        }
                    }
                }
            }

            if (!exprSync.empty()) {
                std::string originalCallText = TheRewriter.getRewrittenText(CE->getSourceRange());
                if (originalCallText.empty()) {
                    originalCallText = clang::Lexer::getSourceText(
                        clang::CharSourceRange::getTokenRange(CE->getSourceRange()), SM, TheRewriter.getLangOpts()).str();
                }

                std::string replacement = "(" + exprSync + originalCallText + ")";
                TheRewriter.ReplaceText(CE->getSourceRange(), replacement);
            }
        }
    }
    return true;
}

bool CodeVisitorAndRewriter::TraverseCompoundStmt(clang::CompoundStmt *CS) {
    if (isPreCheckPhase) {
        return clang::RecursiveASTVisitor<CodeVisitorAndRewriter>::TraverseCompoundStmt(CS);
    }
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    bool isInMain = SM.isInMainFile(CS->getBeginLoc());
    if (tracksBounds() && isInMain) {
        scopeStack.push_back(std::vector<AllocInfo>());
    }

    bool result = clang::RecursiveASTVisitor<CodeVisitorAndRewriter>::TraverseCompoundStmt(CS);

    if (tracksBounds() && isInMain) {
        if (!scopeStack.empty()) {
            if (!hasReturnStmt) {
                std::vector<AllocInfo> &currentScopeAllocations = scopeStack.back();
                std::string freeCodes = "";

                for (const auto &alloc : currentScopeAllocations) {
                    freeCodes += "\n    __Ptr2Arr_len_" + alloc.varName + " = 0;";
                    freeCodes += "\n    __Ptr2Arr_base_" + alloc.varName + " = 0;";
                }

                if (!freeCodes.empty()) {
                    freeCodes += "\n";
                    TheRewriter.InsertTextBefore(CS->getEndLoc(), freeCodes);
                }
            }
            scopeStack.pop_back();
        }
    }

    return result;
}