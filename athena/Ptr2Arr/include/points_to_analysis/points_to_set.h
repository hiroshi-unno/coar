#ifndef POINTS_TO_SET_H
#define POINTS_TO_SET_H

struct ScopedPointer {
    std::string functionName;
    std::string pointerName;
    bool operator==(const ScopedPointer& other) const {
        return functionName == other.functionName && pointerName == other.pointerName;
    }
    bool operator<(const ScopedPointer& other) const {
        if (functionName != other.functionName) return functionName < other.functionName;
        return pointerName < other.pointerName;
    }
};

struct PointsToSet {
    std::vector<ScopedPointer> pointers;
    std::string dataType;
    std::vector<ScopedPointer> pointees;
};

struct PointsToString {
    std::string llvmVarName;
    std::string varName;
    std::string content;
};

#endif //POINTS_TO_SET_H