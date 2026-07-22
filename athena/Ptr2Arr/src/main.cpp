#include "clang/Tooling/Tooling.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include <llvm/IR/LLVMContext.h>
#include "llvm/Support/CommandLine.h"

#include "../include/pointer_visitor/pointer_action.h"
#include "../include/points_to_analysis/points_to_analysis.h"
#include "../include/memory_analysis/memory_analysis.h"
#include "../include/code_visitor_and_rewriter/code_action.h"
#include "../include/bit_expression_visitor_and_rewriter/bit_expression_action.h"
#include "../include/file_writer/file_writer.h"

#include "../include/llvm_var_analysis/llvm_var_analysis.h"

static llvm::cl::opt<std::string> InputFilename(
    llvm::cl::Positional,
    llvm::cl::desc("<path/to/SourceCode.c>"),
    llvm::cl::Required
);

static llvm::cl::opt<std::string> OutputFilename(
    "o",
    llvm::cl::desc("Output C file name"),
    llvm::cl::value_desc("filename"),
    llvm::cl::init("")
);

static std::string ShellQuote(const std::filesystem::path &Path) {
    std::string quoted = "'";
    for (char c : Path.string()) {
        if (c == '\'') {
            quoted += "'\\''";
        } else {
            quoted += c;
        }
    }
    quoted += "'";
    return quoted;
}

int main(int argc, char *argv[]) {
    llvm::cl::ParseCommandLineOptions(argc, argv, "Ptr2Arr - C-to-C rewriter\n");

    std::filesystem::path executablePath = std::filesystem::canonical("/proc/self/exe");
    executableDirectory = executablePath.parent_path();

    std::filesystem::path sourceCodePath = std::filesystem::canonical(InputFilename.getValue());
    std::ifstream sourceCodeStream(sourceCodePath);
    if (!sourceCodeStream) {
        std::cerr << strerror(errno) << ": " << sourceCodePath << std::endl;
        return 1;
    }

    std::vector<std::string> clangArgs = {
        "-xc",
        "-I/usr/lib/llvm-14/lib/clang/14.0.6/include",
        "-Wno-incompatible-library-redeclaration",
        "-Wno-unknown-attributes",
        "-Wno-unused-label",
    };

    sourceCodeName = sourceCodePath.stem().string();
    if (OutputFilename.empty()) {
        outputDirectory = std::filesystem::current_path();
        outputSourcePath = outputDirectory / (sourceCodeName + "_Ptr2Arr.c");
    } else {
        outputSourcePath = OutputFilename.getValue();
        if (outputSourcePath.is_relative()) {
            outputSourcePath = std::filesystem::current_path() / outputSourcePath;
        }
        outputDirectory = outputSourcePath.parent_path();
        if (outputDirectory.empty()) {
            outputDirectory = std::filesystem::current_path();
            outputSourcePath = outputDirectory / outputSourcePath;
        }
    }

    std::error_code createDirectoryError;
    std::filesystem::create_directories(outputDirectory, createDirectoryError);
    if (createDirectoryError) {
        std::cerr << createDirectoryError.message() << ": " << outputDirectory << std::endl;
        return 1;
    }

    std::filesystem::path outputBasePath = outputSourcePath;
    outputBasePath.replace_extension();
    outputBitcodePath = outputBasePath;
    outputBitcodePath.replace_extension(".bc");
    if (OutputFilename.empty()) {
        outputMetadataPath = outputDirectory / (sourceCodeName + "_Metadata_Ptr2Arr.txt");
    } else {
        outputMetadataPath = outputBasePath;
        outputMetadataPath += "_Metadata_Ptr2Arr.txt";
    }
    outputPointsToSetsPath = outputDirectory / (sourceCodeName + "_PointsToSets.txt");
    outputAllocatedMemoryPath = outputDirectory / (sourceCodeName + "_AllocatedMemory_Ptr2Arr.txt");

    WriteToFile("");

    std::ifstream newSourceCodeStream(sourceCodePath);
    std::stringstream sourceCodeBuffer;
    sourceCodeBuffer << newSourceCodeStream.rdbuf();
    std::string sourceCodeFile = sourceCodeBuffer.str();

    std::string command_DG = "clang-14 -g -c -emit-llvm -fno-discard-value-names -Wno-incompatible-library-redeclaration -Wno-unknown-attributes -Wno-unused-label " + ShellQuote(sourceCodePath) + " -o " + ShellQuote(outputBitcodePath) + " && "
                             "llvm-pta-dump -pta fs -ir --names-with-funs " + ShellQuote(outputBitcodePath) + " > " + ShellQuote(outputPointsToSetsPath);
    int result_DG = system(command_DG.c_str());
    if (result_DG != 0) {
        std::cerr << "DG execution failed." << "\n";
        return 1;
    }

    const std::string bcFilePath = outputBitcodePath;
    llvm::LLVMContext llvmContext;
    LLVMVarAnalysis llvmVarAnalysis(llvmContext);
    llvmVarAnalysis.analyze(bcFilePath);
    std::map<std::string, std::map<std::string, std::string>> llvmVarMap = llvmVarAnalysis.getFullMap();
    std::map<std::string, std::vector<std::string>> functionReturnMap = llvmVarAnalysis.getFunctionReturnMap();

    std::cerr << "LLVM IR Variable to C Variable Mapping:\n";
    for (const auto& funcPair : llvmVarMap) {
        const std::string& funcName = funcPair.first;
        const auto& varMap = funcPair.second;
        std::cerr << "Function: " << funcName << "\n";
        for (const auto& varPair : varMap) {
            std::cerr << "  IR Variable: " << varPair.first << " -> C Variable: " << varPair.second << "\n";
        }
    }
    std::cerr << "\n";

    std::cerr << "Function Return Mapping:\n";
    for (const auto& funcPair : functionReturnMap) {
        const std::string& funcName = funcPair.first;
        const auto& returnVars = funcPair.second;
        std::cerr << "Function: " << funcName << " -> Return Variables: [";
        for (const auto& retVar : returnVars) {
            std::cerr << retVar << ", ";
        }        std::cerr << "]\n";
    }
    std::cerr << "\n";

    const std::string pointsToSetsPath = outputPointsToSetsPath;
    std::ifstream pointsToSetsStream(pointsToSetsPath);
    std::stringstream pointsToSetsBuffer;
    pointsToSetsBuffer << pointsToSetsStream.rdbuf();

    std::vector<PointsToSet> pointsToSets;
    std::vector<PointsToString> pointsToStrings;
    clang::tooling::runToolOnCodeWithArgs(std::make_unique<PointerAction>(pointsToSets), sourceCodeFile, clangArgs);

    std::cerr << "PointsToSets after PointerAction:\n";
    for (const auto& pts : pointsToSets) {
        for (const auto& pointer : pts.pointers) {
            std::cerr << "Pointer: " << pointer.functionName << ":" << pointer.pointerName << ", ";
        }
        std::cerr << "DataType: " << pts.dataType << ", Pointees: [";
        for (const auto& pointee : pts.pointees) {
            std::cerr << pointee.functionName << ":" << pointee.pointerName << ", ";
        }
        std::cerr << "]\n";
    }
    std::cerr << "\n";

    PointsToAnalysis pointsToAnalysis(pointsToSetsBuffer, pointsToSets, pointsToStrings);
    pointsToAnalysis.ConstructPointsToSets();
    pointsToAnalysis.ConstructPointsToStrings();

    std::cerr << "PointsToSets after PointsToAnalysis:\n";
    for (const auto& pts : pointsToSets) {
        for (const auto& pointer : pts.pointers) {
            std::cerr << "Pointer: " << pointer.functionName << ":" << pointer.pointerName << ", ";
        }
        std::cerr << "DataType: " << pts.dataType << ", Pointees: [";
        for (const auto& pointee : pts.pointees) {
            std::cerr << pointee.functionName << ":" << pointee.pointerName << ", ";
        }
        std::cerr << "]\n";
    }
    std::cerr << "\n";

    std::vector<PointsToSet> convertedPointsToSets = llvmVarAnalysis.convertPointsToSetsIRToC(pointsToSets);

    std::vector<MemorySet> memorySets;
    MemoryAnalysis memoryAnalysis(convertedPointsToSets, memorySets);
    memoryAnalysis.ConstructMemorySets();
    clang::tooling::runToolOnCodeWithArgs(std::make_unique<CodeAction>(memorySets, pointsToStrings, functionReturnMap), sourceCodeFile, clangArgs);

    std::cerr << "MemorySets after MemoryAnalysis:\n";
    for (const auto& ms : memorySets) {
        std::cerr << "DataType: " << ms.dataType << ", Pointers: [";
        for (const auto& pointer : ms.pointers) {
            std::cerr << pointer.functionName << ":" << pointer.pointerName << ", ";
        }
        std::cerr << "], Pointees: [";
        for (const auto& pointee : ms.pointees) {
            std::cerr << pointee.functionName << ":" << pointee.pointerName << ", ";
        }
        std::cerr << "], Accessed Types: [";
        for (const auto& at : ms.accessedTypes) {
            std::cerr << at << ", ";
        }
        std::cerr << "]\n";
    }
    std::cerr << "\n";

    for (size_t i = 0; i < memorySets.size(); ++i) {
        std::string pointeeId = std::to_string(i);
        for( const auto& pointer : memorySets[i].pointers) {
            if (!pointer.functionName.empty()){
                WriteToAllocatedMemoryFile("memory" + pointeeId);
                break;
            }
        }
    }

    const std::string outPath = outputSourcePath;
    std::ifstream outStream(outPath);
    std::stringstream outBuffer;
    outBuffer << outStream.rdbuf();
    std::string outFile = outBuffer.str();
    clang::tooling::runToolOnCodeWithArgs(std::make_unique<BitExpressionAction>(), outFile, clangArgs);

    return 0;
}