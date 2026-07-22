#ifndef POINTS_TO_ANALYSIS_REFACTORED_H
#define POINTS_TO_ANALYSIS_REFACTORED_H

#include <memory>
#include <string>
#include <vector>

// Forward declarations
namespace llvm {
class Module;
class Value;
} // namespace llvm

struct PointsToSet {
  std::string pointer;
  std::vector<std::string> pointees;
};

class PointsToAnalysisRefactored {
public:
  PointsToAnalysisRefactored(llvm::Module &M, std::vector<PointsToSet> &sets);

  // Use DG library directly instead of parsing text output
  void analyzePointsTo();

private:
  llvm::Module &module;
  std::vector<PointsToSet> &pointsToSets;

  std::string getValueName(llvm::Value *V);
  void addPointee(const std::string &pointer, const std::string &pointee);
};

#endif // POINTS_TO_ANALYSIS_REFACTORED_H
