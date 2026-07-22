#ifndef MEMORY_SET_H
#define MEMORY_SET_H
#include <set>

#include "../points_to_analysis/points_to_set.h"

struct MemorySet {
    std::vector<ScopedPointer> pointers;
    std::string dataType;
    std::vector<ScopedPointer> pointees;
    std::set<std::string> accessedTypes;
};

#endif //MEMORY_SET_H