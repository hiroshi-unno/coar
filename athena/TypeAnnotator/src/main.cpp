#include <regex>
#include <fstream>
#include <sstream>
#include <iostream>
#include <unordered_set>

#include "clang/Tooling/Tooling.h"

#include "../include/info.h"
#include "../include/bit_operation_visitor/bit_operation_action.h"
#include "../include/bit_variable_visitor/bit_variable_action.h"
#include "../include/nondet_variable_visitor/nondet_variable_action.h"

std::string MapName_BitVariable(std::string llFile, std::string cName, std::string declLine) {
    std::string t2Name;
    if (cName.starts_with("gtv_")) {
        std::string gtvUsage;
        std::regex gtvUsagePattern("store .* %\"?([a-zA-Z0-9._]+)\"?, .*\\* @\"'" + cName + "\", align [0-9]+, !dbg ![0-9]+");
        std::smatch gtvUsageMatches;
        std::string::const_iterator gtvUsageSearchStart(llFile.cbegin());
        while (std::regex_search(gtvUsageSearchStart, llFile.cend(), gtvUsageMatches, gtvUsagePattern)) {
            gtvUsage = gtvUsageMatches[1].str();
            break;
        }
        t2Name = "v" + gtvUsage;
    }
    else {
        std::string metadataId;
        std::string metadataUsage;
        std::regex metadataIdPattern("(![0-9]+).*\\[" + cName + "\\] \\[line " + declLine + "\\]");
        std::smatch metadataIdMatches;
        std::string::const_iterator metadataIdSearchStart(llFile.cbegin());
        while (std::regex_search(metadataIdSearchStart, llFile.cend(), metadataIdMatches, metadataIdPattern)) {
            metadataId = metadataIdMatches[1].str();
            break;
        }
        std::regex metadataUsagePattern("call void @llvm\\.dbg\\.value\\(metadata !\\{.* %\"?([a-zA-Z0-9._]+)\"?\\}, .* [0-9]+, metadata " + metadataId + "\\), !dbg ![0-9]+");
        std::smatch metadataUsageMatches;
        std::string::const_iterator metadataUsageSearchStart(llFile.cbegin());
        while (std::regex_search(metadataUsageSearchStart, llFile.cend(), metadataUsageMatches, metadataUsagePattern)) {
            metadataUsage = metadataUsageMatches[1].str();
            break;
        }
        if (metadataUsage.empty()) {
            if (llFile.find("%" + cName + ".0") != std::string::npos) {
                t2Name = "v" + cName + ".0";
            }
        }
        else {
            t2Name = "v" + metadataUsage;
        }
    }
    return t2Name;
}

std::string MapName_NondetVariable(const std::string &llFile, const std::string &cName, const std::string &declLine, size_t i) {
    std::string t2Name;
    std::regex pattern("(%\"?[\\w\\.]+\"?)\\s*=\\s*(tail\\s*)?call\\s+(?:\\w+\\s+)*?(i\\d+)\\s+@__VERIFIER_nondet_(\\w+)\\(\\)(?:[^!]*?)!dbg\\s*!?\\d+");
    std::string mainBody = llFile.substr(llFile.find("define i32 @main()"));
    size_t counter = 0;
    for (std::sregex_iterator it(mainBody.begin(), mainBody.end(), pattern), end; it != end; ++it, ++counter) {
        if (counter == i) {
            t2Name = (*it)[1].str();
            t2Name.erase(std::remove(t2Name.begin(), t2Name.end(), '%'), t2Name.end());
            t2Name.erase(std::remove(t2Name.begin(), t2Name.end(), '"'), t2Name.end());
        }
    }
    return "v" + t2Name;
}

int main(int argc, char *argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: ./TypeAnnotator <path/to/SourceCode_Ptr2Arr.c> <path/to/SourceCode_llvm2KITTeL.ll> --mode=none/only-bv/only-nobv/all\n";
        return 1;
    }

    std::filesystem::path cPath = std::filesystem::canonical(argv[1]);
    std::ifstream cStream(cPath);
    if (!cStream) {
        std::cerr << strerror(errno) << ": " << cPath << std::endl;
        return 1;
    }
    std::stringstream cBuffer;
    cBuffer << cStream.rdbuf();
    std::string cFile = cBuffer.str();

    std::filesystem::path llPath = std::filesystem::canonical(argv[2]);
    std::ifstream llStream(llPath);
    if (!llStream) {
        std::cerr << strerror(errno) << ": " << llPath << std::endl;
        return 1;
    }
    std::stringstream llBuffer;
    llBuffer << llStream.rdbuf();
    std::string llFile = llBuffer.str();

    std::filesystem::path t2Path = std::filesystem::canonical(argv[3]);
    std::ifstream t2File(t2Path);
    if (!t2File) {
        std::cerr << strerror(errno) << ": " << t2Path << std::endl;
        return 1;
    }

    std::string mode = argv[4];

    sourceCodeName = t2Path.stem().string();
    outputDirectory = std::filesystem::current_path();

    const std::string outPath = outputDirectory / (sourceCodeName + "_annotated.t2");
    std::ofstream outFile(outPath, std::ios::trunc);
    if (!outFile) {
        std::cerr << strerror(errno) << ": " << outPath << std::endl;
        return 1;
    }



    std::string line;
    int t2FileLineCount = 0;
    while (t2FileLineCount < 2 && std::getline(t2File, line)) {
        outFile << line << "\n";
        t2FileLineCount = t2FileLineCount + 1;
    }
    outFile << "\n";

    if (mode == "--mode=none") {
        outFile << "\n";
    }

    else if (mode == "--mode=only-bv") {
        bool hasBitOperation = false;
        clang::tooling::runToolOnCode(std::make_unique<BitOperationAction>(hasBitOperation), cFile);
        if (hasBitOperation) {
            std::vector<BitVariable> bitVariables;
            clang::tooling::runToolOnCode(std::make_unique<BitVariableAction>(bitVariables), cFile);
            std::set<std::string> uniqueTypes;
            for (const auto &item : bitVariables) {
                std::string cName = item.name;
                std::string declLine = std::to_string(item.declLine + (cName.starts_with("gtv_") ? 1 : 11));
                std::string bitwidth = item.bitwidth;
                std::string signedness = item.signedness;
                std::string t2Name = MapName_BitVariable(llFile, cName, declLine);
                if (!t2Name.empty()) {
                    uniqueTypes.insert("TYPE " + t2Name + ": bv(" + bitwidth + ");");
                }
            }
            for (const auto& type : uniqueTypes) {
                outFile << type << "\n";
            }
        }
        else {
            outFile << "\n";
        }
    }

    else if (mode == "--mode=only-nobv") {
        bool hasBitOperation = false;
        clang::tooling::runToolOnCode(std::make_unique<BitOperationAction>(hasBitOperation), cFile);
        if (hasBitOperation) {
            outFile << "\n";
        }
        else {
            std::vector<NondetVariable> nondetVariables;
            clang::tooling::runToolOnCode(std::make_unique<NondetVariableAction>(nondetVariables), cFile);
            std::set<std::string> uniqueTypes;
            for (size_t i = 0; i < nondetVariables.size(); ++i) {
                const auto &item = nondetVariables[i];
                std::string cName = item.name;
                std::string declLine = std::to_string(item.declLine + (cName.starts_with("gtv_") ? 1 : 11));
                std::string bitwidth = item.bitwidth;
                std::string signedness = item.signedness;
                std::string t2Name = MapName_NondetVariable(llFile, cName, declLine, i);
                if (!t2Name.empty()) {
                    uniqueTypes.insert("TYPE " + t2Name + ": bv(" + bitwidth + ");");
                }
            }
            for (const auto& type : uniqueTypes) {
                outFile << type << "\n";
            }
        }
    }

    else if (mode == "--mode=all") {
        bool hasBitOperation = false;
        clang::tooling::runToolOnCode(std::make_unique<BitOperationAction>(hasBitOperation), cFile);
        if (hasBitOperation) {
            std::vector<BitVariable> bitVariables;
            clang::tooling::runToolOnCode(std::make_unique<BitVariableAction>(bitVariables), cFile);
            std::set<std::string> uniqueTypes;
            for (const auto &item : bitVariables) {
                std::string cName = item.name;
                std::string declLine = std::to_string(item.declLine + (cName.starts_with("gtv_") ? 1 : 11));
                std::string bitwidth = item.bitwidth;
                std::string signedness = item.signedness;
                std::string t2Name = MapName_BitVariable(llFile, cName, declLine);
                if (!t2Name.empty()) {
                    uniqueTypes.insert("TYPE " + t2Name + ": bv(" + bitwidth + ");");
                }
            }
            for (const auto& type : uniqueTypes) {
                outFile << type << "\n";
            }
        }
        else {
            std::vector<NondetVariable> nondetVariables;
            clang::tooling::runToolOnCode(std::make_unique<NondetVariableAction>(nondetVariables), cFile);
            std::set<std::string> uniqueTypes;
            for (size_t i = 0; i < nondetVariables.size(); ++i) {
                const auto &item = nondetVariables[i];
                std::string cName = item.name;
                std::string declLine = std::to_string(item.declLine + (cName.starts_with("gtv_") ? 1 : 11));
                std::string bitwidth = item.bitwidth;
                std::string signedness = item.signedness;
                std::string t2Name = MapName_NondetVariable(llFile, cName, declLine, i);
                if (!t2Name.empty()) {
                    uniqueTypes.insert("TYPE " + t2Name + ": bv(" + bitwidth + ");");
                }
            }
            for (const auto& type : uniqueTypes) {
                outFile << type << "\n";
            }
        }
    }

    outFile << "\n";
    while (std::getline(t2File, line)) {
        outFile << line << "\n";
    }

    t2File.close();
    outFile.close();

    return 0;
}