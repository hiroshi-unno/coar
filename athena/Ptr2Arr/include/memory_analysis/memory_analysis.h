#ifndef MEMORY_ANALYSIS_H
#define MEMORY_ANALYSIS_H

#include <regex>
#include <fstream>
#include <sstream>
#include <iostream>

#include "../points_to_analysis/points_to_set.h"
#include "memory_set.h"

class MemoryAnalysis {
public:
    explicit MemoryAnalysis(const std::vector<PointsToSet> &pointsToSets, std::vector<MemorySet> &memorySets) : pointsToSets(pointsToSets), memorySets(memorySets) {}

    void ConstructMemorySets();
    bool HasIntersection(const std::vector<ScopedPointer>& set1, const std::vector<ScopedPointer>& set2);
    bool HasSubset(const std::vector<ScopedPointer>& subset, const std::vector<ScopedPointer>& superset);
    bool IsSubsetForPointeesOfPointsToSets(const std::vector<ScopedPointer>& subset);
    bool IsSubsetForPointeesOfMemorySets(const std::vector<ScopedPointer>& subset);
    void MergeMemorySets(MemorySet& target, PointsToSet& source);
    void Merge(std::vector<ScopedPointer>& target, const ScopedPointer& source );
    void Merge(std::vector<ScopedPointer>& target, const std::vector<ScopedPointer>& source);

private:
    std::vector<PointsToSet> pointsToSets;
    std::vector<MemorySet> &memorySets;
};

#endif //MEMORY_ANALYSIS_H