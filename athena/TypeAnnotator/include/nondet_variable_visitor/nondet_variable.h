#ifndef NONDET_VARIABLE_H
#define NONDET_VARIABLE_H

struct NondetVariable {
    std::string name;
    unsigned int declLine;
    std::string bitwidth;
    std::string signedness;
};

#endif //NONDET_VARIABLE_H