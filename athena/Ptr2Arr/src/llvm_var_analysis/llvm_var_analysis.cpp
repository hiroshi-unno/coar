#include "../../include/llvm_var_analysis/llvm_var_analysis.h"
#include "../../include/points_to_analysis/points_to_set.h"

#include <llvm/IR/InstIterator.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/DebugInfoMetadata.h>

std::vector<std::string> getOriginalNameRecursive(llvm::Value *V, std::map<std::string, std::string> &varMap, std::set<llvm::Value*> &visited)
{
    // Prevent infinite loops from cyclic references
    if (!V || visited.count(V))
        return {};

    visited.insert(V);

    std::vector<std::string> results;

    if (V->hasName())
    {
        std::string name = V->getName().str();
        if (varMap.count(name))
            return {varMap.at(name)};
    }

    if (auto *I = llvm::dyn_cast<llvm::Instruction>(V))
    {
        if (llvm::isa<llvm::BitCastInst>(I))
        {
            // ex. "%var1 = bitcast i32* %var.addr to i8*"
            return getOriginalNameRecursive(I->getOperand(0), varMap, visited);
        }
        else if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(I))
        {
            // TODO: handle struct field accesses if needed.
            if (GEP->getPointerOperandType()->getPointerElementType()->isStructTy()) {
                return {};
            }
            // ex. "%var2 = getelementptr inbounds [10 x i32], [10 x i32]* %arr, i64 0, i64 5"
            return getOriginalNameRecursive(GEP->getPointerOperand(), varMap, visited);
        }
        else if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(I))
        {
            // ex. "%10 = load %struct.Node*, %struct.Node** %head, align 8"
            llvm::Value *ptrOp = LI->getPointerOperand();
            return getOriginalNameRecursive(ptrOp, varMap, visited);
        }
        else if (auto *CI = llvm::dyn_cast<llvm::CallInst>(I))
        {
            if (auto *callee = CI->getCalledFunction())
            {
                return {callee->getName().str()};
            }
        }
        else if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(I))
        {
            bool found_store = false;
            // Iterate through all users of this AllocaInst
            for (auto *U : AI->users())
            {
                if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
                {
                    // Check if this StoreInst is writing TO this AllocaInst
                    if (SI->getPointerOperand() == AI)
                    {
                        // Recursively trace the value being stored
                        auto res = getOriginalNameRecursive(SI->getValueOperand(), varMap, visited);
                        results.insert(results.end(), res.begin(), res.end());
                        found_store = true;
                    }
                }
            }
            if (!found_store) {
                std::string irName;
                llvm::raw_string_ostream os(irName);
                AI->printAsOperand(os, false);
                if (!irName.empty() && irName[0] == '%')
                {
                    irName = irName.substr(1);
                }
                results.push_back("alloca_" + irName);
            }
        }
        else if (auto *PN = llvm::dyn_cast<llvm::PHINode>(I))
        {
            for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i)
            {
                auto res = getOriginalNameRecursive(PN->getIncomingValue(i), varMap, visited);
                results.insert(results.end(), res.begin(), res.end());
            }
        }
        else
        {
            // TODO: handle more instruction types if needed
            return {};
        }
    }else if(llvm::isa<llvm::ConstantPointerNull>(V))
    {
        results.push_back("null");
    }

    std::sort(results.begin(), results.end());
    results.erase(std::unique(results.begin(), results.end()), results.end());

    return results;
}

std::vector<std::string> getOriginalName(llvm::Value *V, std::map<std::string, std::string> &varMap)
{
    std::set<llvm::Value*> visited;
    return getOriginalNameRecursive(V, varMap, visited);
}

void LLVMVarAnalysis::analyze(const std::string &bcFilePath)
{
    // parse the .bc file and build the module
    llvm::SMDiagnostic err;
    module = llvm::parseIRFile(bcFilePath, err, context);

    if (!module)
    {
        llvm::errs() << "Error parsing bitcode file: " << err.getMessage() << "\n";
        return;
    }

    // reset the variable map
    varMap.clear();

    for (auto &G : module->globals()) {
        if (G.hasName()) {
            std::string irName = G.getName().str();

            // if irName starts with ".str", it's a string literal, we can keep the original name as is
            if (irName.find(".str") == 0) {
                varMap[""][irName] = "@" + irName; // ".str0" -> "@.str0"
                continue;
            }

            varMap[""][irName] = irName;
        }
    }

    // traverse all functions and instructions to find llvm.dbg.declare calls
    for (auto &F : *module)
    {
        std::string funcName = F.getName().str();
        for (auto &I : llvm::instructions(F))
        {
            // Handle malloc calls to map them to "malloc" in C
            if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
                if (auto *Callee = CI->getCalledFunction()) {
                    if (Callee->getName() == "malloc" && CI->hasName()) {
                        std::string irName = CI->getName().str();
                       varMap[funcName][irName] = "malloc";
                    }
                }
            }

            if (auto *DDI = llvm::dyn_cast<llvm::DbgDeclareInst>(&I))
            {
                // get the IR variable (the operand of llvm.dbg.declare)
                llvm::Value *irVal = DDI->getAddress();

                // get the variable name metadata
                llvm::DILocalVariable *varMD = DDI->getVariable();

                if (irVal && irVal->hasName() && varMD)
                {
                    std::string irName = irVal->getName().str(); // ex. "%var.addr"
                    std::string cName = varMD->getName().str();  // ex. "var"

                    varMap[funcName][irName] = cName;
                }
            }
        }
    }

    for (auto &F : *module)
    {
        std::string funcName = F.getName().str();
        for (auto &I : llvm::instructions(F))
        {
            if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I))
            {
                if (llvm::Value *retVal = RI->getReturnValue())
                {
                    if (retVal->getType()->isPointerTy())
                    {
                        std::vector<std::string> originNames = getOriginalName(retVal, varMap[funcName]);
                        for (const std::string &origin : originNames)
                        {
                            if (!origin.empty())
                            {
                                functionReturnMap[funcName].push_back(origin);
                            }
                        }
                    }
                }
            }
            else if (!llvm::isa<llvm::DbgDeclareInst>(&I))
            {
                std::string irName;
                llvm::raw_string_ostream os(irName);
                I.printAsOperand(os, false);

                if (!irName.empty() && irName[0] == '%')
                {
                    irName = irName.substr(1);
                }

                if (!irName.empty())
                {
                    // Skip if already mapped in Pass 1
                    if (varMap[""].count(irName) || varMap[funcName].count(irName))
                        continue;

                    std::vector<std::string> originNames = getOriginalName(&I, varMap[funcName]);

                    if (!originNames.empty())
                    {
                        std::string chosenName = originNames.front();
                        for (const auto &name : originNames)
                        {
                            if (name != "null" && name != "alloca")
                            {
                                chosenName = name;
                                break;
                            }
                        }
                        varMap[funcName][irName] = chosenName;
                    }
                }
            }
        }
    }

    return;
}

std::vector<PointsToSet> LLVMVarAnalysis::convertPointsToSetsIRToC(const std::vector<PointsToSet> &pointsToSets) const
{
    std::vector<PointsToSet> convertedSets;
    convertedSets.clear();

    for (const auto &ptrSet : pointsToSets)
    {
        PointsToSet convertedSet;
        convertedSet.dataType = ptrSet.dataType;
        convertedSet.pointees.clear();
        convertedSet.pointers.clear();

        for (const auto &ptr : ptrSet.pointers) {
            std::string funcName = ptr.functionName;
            std::string irName = ptr.pointerName;

            if (varMap.count(funcName) && varMap.at(funcName).count(irName))
            {
                std::string cName = varMap.at(funcName).at(irName);
                if (cName == "malloc") {
                    convertedSet.pointers.push_back({"", "malloc"});
                } else if (cName == "alloca") {
                    convertedSet.pointers.push_back({funcName, "alloca_" + irName});
                } else {
                    convertedSet.pointers.push_back({funcName, cName});
                }
            }else{
                continue;
            }
        }
        for (const auto &pointee : ptrSet.pointees)
        {
            std::string pfuncName = pointee.functionName;
            std::string pirName = pointee.pointerName;

            if (varMap.count(pfuncName) && varMap.at(pfuncName).count(pirName))
            {
                std::string cName = varMap.at(pfuncName).at(pirName);
                if (cName == "malloc") {
                   convertedSet.pointees.push_back({"", "malloc"});
                } else if (cName == "alloca") {
                    convertedSet.pointees.push_back({pfuncName, "alloca_" + pirName});
                } else {
                    convertedSet.pointees.push_back({pfuncName, cName});
                }
            }
        }
        convertedSets.push_back(convertedSet);
    }
    return convertedSets;
}