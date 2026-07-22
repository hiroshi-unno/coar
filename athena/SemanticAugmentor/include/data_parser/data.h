#ifndef DATA_H
#define DATA_H

struct FunctionParameter {
    std::string functionName;
    std::string parameterName;
};

struct LocalVariable {
    std::string functionName;
    std::string variableName;
};

struct Data {
    std::vector<std::string> macros;
    std::vector<std::string> structureFields;
    std::vector<std::string> functions;
    std::vector<FunctionParameter> functionParameters;
    std::vector<std::string> globalVariables;
    std::vector<LocalVariable> localVariables;
};

#endif //DATA_H