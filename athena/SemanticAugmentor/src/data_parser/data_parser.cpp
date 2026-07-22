#include "../../include/data_parser/data_parser.h"

void DataParser::ParseData(){
    std::string line;
    while (std::getline(txtFile, line)) {
        std::vector<std::string> tokens;
        size_t start = 0;
        size_t end = line.find(", ");
        while (end != std::string::npos) {
            tokens.push_back(line.substr(start, end - start));
            start = end + 2;
            end = line.find(", ", start);
        }
        tokens.push_back(line.substr(start));
        const std::string &token1 = tokens[0];
        const std::string &token2 = tokens[1];
        const std::string &token3 = (tokens.size() > 2) ? tokens[2] : "";
        if (token1 == "Macro") {
            data.macros.push_back(token2);
        }
        else if (token1 == "StructureField") {
            data.structureFields.push_back(token2);
        }
        else if (token1 == "Function") {
            data.functions.push_back(token2);
        }
        else if (token1 == "FunctionParameter") {
            data.functionParameters.push_back({token2, token3});
        }
        else if (token1 == "GlobalVariable") {
            data.globalVariables.push_back(token2);
        }
        else if (token1 == "LocalVariable") {
            data.localVariables.push_back({token2, token3});
        }
    }
}