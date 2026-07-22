#ifndef BIT_VARIABLE_H
#define BIT_VARIABLE_H

struct BitVariable {
    std::string name;
    unsigned int declLine;
    std::string bitwidth;
    std::string signedness;
};

#endif //BIT_VARIABLE_H