#ifndef LLVM_VAR_ANALYSIS_H
#define LLVM_VAR_ANALYSIS_H

#include <map>
#include <string>
#include <memory>

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Value.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/InstIterator.h>

#include "../../include/points_to_analysis/points_to_set.h"

class LLVMVarAnalysis
{
public:
    explicit LLVMVarAnalysis(llvm::LLVMContext &context) : context(context) {}

    // Analyze the .bc file to build the mapping from LLVM IR variable names to C variable names
    void analyze(const std::string &bcFilePath);

    // Map from function name -> IR variable name -> C variable name
    const std::map<std::string, std::map<std::string, std::string>> &getFullMap() const { return varMap; }
    const std::map<std::string, std::vector<std::string>> &getFunctionReturnMap() const { return functionReturnMap; }

    std::vector<PointsToSet> convertPointsToSetsIRToC(const std::vector<PointsToSet> &pointsToSets) const;

private:
    llvm::LLVMContext &context;
    std::unique_ptr<llvm::Module> module;
    std::map<std::string, std::map<std::string, std::string>> varMap; // func name ->IR variable name -> C variable name
    std::map<std::string, std::vector<std::string>> functionReturnMap;
};

#endif // LLVM_VAR_ANALYSIS_H