#ifndef POINTS_TO_ANALYSIS_H
#define POINTS_TO_ANALYSIS_H

#include <regex>
#include <sstream>
#include <iostream>
#include <set>

#include "../file_writer/info.h"
#include "points_to_set.h"

class PointsToAnalysis {
public:
    explicit PointsToAnalysis(std::stringstream &pointsToSetsBuffer, std::vector<PointsToSet> &pointsToSets, std::vector<PointsToString> &pointsToStrings)
    : pointsToSetsBuffer(pointsToSetsBuffer), pointsToSets(pointsToSets), pointsToStrings(pointsToStrings) {}

    void ConstructPointsToSets();
    void ConstructPointsToStrings();

private:
    std::stringstream &pointsToSetsBuffer;
    std::vector<PointsToSet> &pointsToSets;
    std::vector<PointsToString> &pointsToStrings;

    void CollectBasePointsTo(std::map<std::string, std::map<std::string, std::vector<ScopedPointer>>> &baseMap);
    void ResolveStoresAndLoads(const std::map<std::string, std::map<std::string, std::vector<ScopedPointer>>> &baseMap);
    void UnifyAssignmentEquivalenceClasses();
    void UnifyFunctionArgsEquivalenceClasses();

    std::string decodeLLVMString(const std::string& input);
};

#endif //POINTS_TO_ANALYSIS_H