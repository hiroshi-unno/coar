#include "../../include/memory_analysis/memory_analysis.h"
#include "llvm/Support/raw_ostream.h"

void MemoryAnalysis::ConstructMemorySets() {

    std::vector<PointsToSet> workingSets = pointsToSets;

    while (!workingSets.empty()) {
        PointsToSet currentSet = workingSets.back();
        workingSets.pop_back();
        bool isMerged = false;
        for (auto& memorySet : memorySets) {
            if (HasIntersection(memorySet.pointees, currentSet.pointees)) {
                MergeMemorySets(memorySet, currentSet);
                isMerged = true;
            }else{
                // check if there exists a pointee set Q s.t. {currentSet.pointer, p_j} is a subset of Q for some p_j in memorySet.pointers
                for (const auto& pointer : memorySet.pointers) {
                    for (const auto& currPtr : currentSet.pointers) {
                        if (IsSubsetForPointeesOfPointsToSets({currPtr, pointer}) || IsSubsetForPointeesOfMemorySets({currPtr, pointer})) {
                            MergeMemorySets(memorySet, currentSet);
                            isMerged = true;
                        }
                    }
                }
            }
        }
        if (!isMerged) {
            MemorySet newSet;
            Merge(newSet.pointers, currentSet.pointers);
            newSet.dataType = currentSet.dataType;
            newSet.accessedTypes.insert(currentSet.dataType);
            Merge(newSet.pointees, currentSet.pointees);
            memorySets.push_back(newSet);
        }
    }
}

bool MemoryAnalysis::HasIntersection(const std::vector<ScopedPointer>& set1, const std::vector<ScopedPointer>& set2) {
    for (const auto& item : set1) {
        if (std::find(set2.begin(), set2.end(), item) != set2.end()) {
            return true;
        }
    }
    return false;
}

bool MemoryAnalysis::HasSubset(const std::vector<ScopedPointer>& subset, const std::vector<ScopedPointer>& superset) {
    for (const auto& item : subset) {
        if (std::find(superset.begin(), superset.end(), item) == superset.end()) {
            return false;
        }
    }
    return true;
}

bool MemoryAnalysis::IsSubsetForPointeesOfPointsToSets(const std::vector<ScopedPointer>& subset) {
    bool hasPointeeSubset = false;
    for (const auto& pointsToSet: pointsToSets) {
        if (HasSubset(subset, pointsToSet.pointees)) {
            hasPointeeSubset = true;
            break;
        }
    }
    return hasPointeeSubset;
}

bool MemoryAnalysis::IsSubsetForPointeesOfMemorySets(const std::vector<ScopedPointer>& subset) {
    bool hasPointeeSubset = false;
    for (const auto& memorySet: memorySets) {
        if (HasSubset(subset, memorySet.pointees)) {
            hasPointeeSubset = true;
            break;
        }
    }
    return hasPointeeSubset;
}

void MemoryAnalysis::MergeMemorySets(MemorySet& target, PointsToSet& source) {

    Merge(target.pointers, source.pointers);

    if (!source.dataType.empty()) {
        target.accessedTypes.insert(source.dataType);
    }

    // If there are multiple accessed types, we coerce to unsigned char and print a warning.
    if (target.accessedTypes.size() > 1)
    {
        if (target.dataType != "unsigned char") {
            llvm::errs() << "[Ptr2Arr] Information: this memorySet is accessed with multiple types: ";
            for (const auto& type : target.accessedTypes) {
                llvm::errs() << "'" << type << "' ";
            }
            llvm::errs() << "\n";
            target.dataType = "unsigned char";
        }
    }
    else if (!source.dataType.empty())
    {
        target.dataType = source.dataType;
    }
    Merge(target.pointees, source.pointees);

    auto it = std::remove_if(memorySets.begin(), memorySets.end(), [&](const auto& ms) {
        if (&ms == &target) {
            return false;
        }

        // Check if there's any overlap in pointers between the current memory set and the source points-to set
        bool hasOverlap = false;
        for (const auto& srcPtr : source.pointers) {
            if (std::find(ms.pointers.begin(), ms.pointers.end(), srcPtr) != ms.pointers.end()) {
                hasOverlap = true;
                break; // Stop checking further if at least one common pointer is found
            }
        }

        if (hasOverlap) {
            Merge(target.pointers, ms.pointers);
            target.accessedTypes.insert(ms.accessedTypes.begin(), ms.accessedTypes.end());
            if (!target.dataType.empty() && target.dataType != ms.dataType) {
                llvm::errs() << "[Ptr2Arr] Information: this memorySet is accessed with multiple types: '"
                            << target.dataType << "' and '" << ms.dataType << "'\n";
                target.dataType = "unsigned char";
            } else {
                target.dataType = ms.dataType;
            }
            Merge(target.pointees, ms.pointees);
            return true;
        }
        return false;
    });
    memorySets.erase(it, memorySets.end());
}

void MemoryAnalysis::Merge(std::vector<ScopedPointer>& target, const ScopedPointer& source ) {
    if (std::find(target.begin(), target.end(), source) == target.end()) {
        target.push_back(source);
    }
}

void MemoryAnalysis::Merge(std::vector<ScopedPointer>& target, const std::vector<ScopedPointer>& source) {
    for (const auto &item : source) {
        Merge(target, item);
    }
}