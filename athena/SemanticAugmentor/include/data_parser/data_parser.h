#ifndef DATA_PARSER_H
#define DATA_PARSER_H

#include <regex>
#include <fstream>
#include <iostream>

#include "data.h"

class DataParser {
public:
    explicit DataParser(std::ifstream &txtFile, Data &data) : txtFile(txtFile), data(data) {}

    void ParseData();

private:
    std::ifstream &txtFile;
    Data &data;
};

#endif //DATA_PARSER_H