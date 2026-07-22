#include "clang/Tooling/Tooling.h"

#include "../include/bit_operation_visitor/bit_operation_action.h"
#include "../include/data_parser/data_parser.h"
#include "../include/brace_visitor_and_rewriter/brace_action.h"
#include "../include/code_visitor_and_rewriter/code_action.h"

int main(int argc, char *argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: ./SemanticAugmentor <path/to/SourceCode_Ptr2Arr.c> <path/to/Metadata_Ptr2Arr.txt> --mode=none/only-bv/only-nobv/all\n";
        return 1;
    }

    std::filesystem::path cPath = std::filesystem::canonical(argv[1]);
    sourceCodeName = cPath.stem().string();
    outputDirectory = std::filesystem::current_path();

    std::ifstream cStream(cPath);
    if (!cStream) {
        std::cerr << strerror(errno) << ": " << cPath << std::endl;
        return 1;
    }
    std::stringstream cBuffer;
    cBuffer << cStream.rdbuf();
    std::string cFile = cBuffer.str();

    std::filesystem::path txtPath = std::filesystem::canonical(argv[2]);
    std::ifstream txtFile(txtPath);
    if (!txtFile) {
        std::cerr << strerror(errno) << ": " << txtPath << std::endl;
        return 1;
    }

    std::string mode = argv[3];

    if (mode == "--mode=none") {
        std::ofstream outFile(outputDirectory / (sourceCodeName + "_SemanticAugmentor.c"), std::ios::trunc);
        outFile << cBuffer.str();
    }

    else if (mode == "--mode=only-bv") {
        bool hasBitOperation = false;
        clang::tooling::runToolOnCode(std::make_unique<BitOperationAction>(hasBitOperation), cFile);
        if (hasBitOperation) {
            Data data;
            DataParser dataParser(txtFile, data);
            dataParser.ParseData();
            const std::string outPath = outputDirectory / (sourceCodeName + "_SemanticAugmentor.c");
            clang::tooling::runToolOnCode(std::make_unique<BraceAction>(), cFile);
            std::ifstream outStream(outPath);
            std::stringstream outBuffer;
            outBuffer << outStream.rdbuf();
            std::string outFile = outBuffer.str();
            clang::tooling::runToolOnCode(std::make_unique<CodeAction>(data), outFile);
        }
        else {
            std::ofstream outFile(outputDirectory / (sourceCodeName + "_SemanticAugmentor.c"), std::ios::trunc);
            outFile << cBuffer.str();
        }
    }

    else if (mode == "--mode=only-nobv") {
        bool hasBitOperation = false;
        clang::tooling::runToolOnCode(std::make_unique<BitOperationAction>(hasBitOperation), cFile);
        if (hasBitOperation) {
            // std::ofstream outFile(outputDirectory / (sourceCodeName + "_SemanticAugmentor.c"), std::ios::trunc);
            // outFile << cBuffer.str();
            std::cerr << "Bit-operations not supported." << "\n";
            return 1;
        }
        else {
            Data data;
            DataParser dataParser(txtFile, data);
            dataParser.ParseData();
            const std::string outPath = outputDirectory / (sourceCodeName + "_SemanticAugmentor.c");
            clang::tooling::runToolOnCode(std::make_unique<BraceAction>(), cFile);
            std::ifstream outStream(outPath);
            std::stringstream outBuffer;
            outBuffer << outStream.rdbuf();
            std::string outFile = outBuffer.str();
            clang::tooling::runToolOnCode(std::make_unique<CodeAction>(data), outFile);
        }
    }

    else if (mode == "--mode=all") {
        Data data;
        DataParser dataParser(txtFile, data);
        dataParser.ParseData();
        const std::string outPath = outputDirectory / (sourceCodeName + "_SemanticAugmentor.c");
        clang::tooling::runToolOnCode(std::make_unique<BraceAction>(), cFile);
        std::ifstream outStream(outPath);
        std::stringstream outBuffer;
        outBuffer << outStream.rdbuf();
        std::string outFile = outBuffer.str();
        clang::tooling::runToolOnCode(std::make_unique<CodeAction>(data), outFile);
    }

    return 0;
}