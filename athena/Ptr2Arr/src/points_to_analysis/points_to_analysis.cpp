#include "../../include/points_to_analysis/points_to_analysis.h"

void PointsToAnalysis::CollectBasePointsTo(
    std::map<std::string, std::map<std::string, std::vector<ScopedPointer>>> &baseMap)
{
    std::istringstream stream(pointsToSetsBuffer.str());
    std::string line;
    std::string currentScope = "";
    std::string currentVar = "";

    // Regex to match definitions: NODE \d+: (Scope: )?%VarName ...
    std::regex nodeRegex(R"(NODE\s+\d+:\s+(?:([a-zA-Z_][\w\.]*):\s+)?(?:.*?\s+)?([%@][\w\.]+)(?:\s*=|\s*\(points-to))");
    // Regex to match pointees: -> (Scope: )?%VarName
    std::regex ptrRegex(R"(\s*->\s*(?:([a-zA-Z_][\w\.]*):\s+)?([%@][\w\.]+))");
    std::regex nullRegex(R"(\s*->\s*null)");

    while (std::getline(stream, line))
    {
        std::smatch m;
        if (std::regex_search(line, m, nodeRegex))
        {
            currentScope = m[1].matched ? m.str(1) : ""; // Global if no scope
            currentVar = m.str(2);
            if (!currentVar.empty() && currentVar[0] == '%') currentVar = currentVar.substr(1);
            if (!currentVar.empty() && currentVar[0] == '@') currentVar = currentVar.substr(1);
        }
        // Parse points-to target line
        else if (line.find("->") != std::string::npos && !currentVar.empty())
        {
            if (std::regex_search(line, m, nullRegex))
            {
                ScopedPointer sp = {"", "null"};
                if (std::find(baseMap[currentScope][currentVar].begin(), baseMap[currentScope][currentVar].end(), sp) == baseMap[currentScope][currentVar].end())
                    baseMap[currentScope][currentVar].push_back(sp);
            }
            else if (std::regex_search(line, m, ptrRegex))
            {
                std::string targetScope = m[1].matched ? m.str(1) : "";
                std::string targetVar = m.str(2);
                if (!targetVar.empty() && targetVar[0] == '%') targetVar = targetVar.substr(1);
                if (!targetVar.empty() && targetVar[0] == '@') targetVar = targetVar.substr(1);

                ScopedPointer sp = {targetScope, targetVar};
                if (std::find(baseMap[currentScope][currentVar].begin(), baseMap[currentScope][currentVar].end(), sp) == baseMap[currentScope][currentVar].end())
                    baseMap[currentScope][currentVar].push_back(sp);
            }
        }
    }
}

void PointsToAnalysis::ResolveStoresAndLoads(
    const std::map<std::string, std::map<std::string, std::vector<ScopedPointer>>> &baseMap)
{

    std::smatch pointerMatches;
    std::smatch pointeeMatches;

    std::regex pointeePattern_null = std::regex(R"(\s*->\s*null .+?)");
    std::regex pointeePattern_newLine = std::regex(R"(\s*->\s*(@..+?) = private unnamed_addr constant \[.+? x .+?\] .+?, align .+? .+?)");
    std::regex pointeePattern_variable = std::regex(R"(\s*->\s*(?:[a-zA-Z_][\w\.]*:\s+)?%(.+?) = alloca .+?, align .+? .+?)");
    std::regex pointeePattern_array = std::regex(R"(\s*->\s*(?:[a-zA-Z_][\w\.]*:\s+)?%(.+?) = alloca \[.+? x .+?\], align .+? .+?)");
    std::regex pointeePattern_alloca = std::regex(R"(\s*->\s*(?:[a-zA-Z_][\w\.]*:\s+)?%(.+?) = alloca .+?, .+? .+?, align .+? .+?)");
    std::regex pointeePattern_malloc = std::regex(R"(\s*->\s*(?:[a-zA-Z_][\w\.]*:\s+)?%(.+?) = call .+?\* @malloc\(.+? .+?\) .+?)");

    for (size_t i = 0; i < pointsToSets.size(); i++)
    {
        for (const auto &ptr : pointsToSets[i].pointers)
        {
            std::string func = ptr.functionName;
            std::string name = ptr.pointerName;

            // Propagate direct points-to relations from baseMap
            if (baseMap.count(func) && baseMap.at(func).count(name))
            {
                for (const auto &obj : baseMap.at(func).at(name))
                {
                    if (obj.pointerName == name && obj.functionName == func) continue;
                    if (std::find(pointsToSets[i].pointees.begin(), pointsToSets[i].pointees.end(), obj) == pointsToSets[i].pointees.end())
                    {
                        pointsToSets[i].pointees.push_back(obj);
                    }
                }
            }

            // Handle store instructions with optional scope prefix
            std::regex pointerStorePattern = std::regex("NODE\\s*.+?:\\s*(?:[a-zA-Z_][\\w\\.]*:\\s+)?store\\s+.+?\\*\\s+[%@](.+?),\\s*.+?\\*\\*\\s+[%@]" + name + ",.*\\(points-to size: (.+?)\\)");
            std::string current_buffer_str = pointsToSetsBuffer.str();
            auto store_begin = std::sregex_iterator(current_buffer_str.begin(), current_buffer_str.end(), pointerStorePattern);
            auto store_end = std::sregex_iterator();

            for (std::sregex_iterator it = store_begin; it != store_end; ++it)
            {
                std::smatch match = *it;
                std::string srcVar = match.str(1);

                // Copy pointees from srcVar to current pointer
                if (baseMap.count(func) && baseMap.at(func).count(srcVar))
                {
                    for (const auto &obj : baseMap.at(func).at(srcVar))
                    {
                        if (std::find(pointsToSets[i].pointees.begin(), pointsToSets[i].pointees.end(), obj) == pointsToSets[i].pointees.end())
                        {
                            pointsToSets[i].pointees.push_back(obj);
                        }
                    }
                }
            }

            // Handle load instructions with optional scope prefix
            std::regex pointerPattern = std::regex("NODE\\s*.+?:\\s*(?:[a-zA-Z_][\\w\\.]*:\\s+)?[%@].+? = load .+?\\*, .+?\\*\\* [%@]" + name + ", align .+? \\(points-to size: .+?\\)\\n");
            std::string tempFile = pointsToSetsBuffer.str();
            while (std::regex_search(tempFile, pointerMatches, pointerPattern))
            {
                if (pointerMatches.size() > 0)
                {
                    std::istringstream stream(pointerMatches.suffix().str());
                    std::string line;
                    while (std::getline(stream, line) && line.find("->") != std::string::npos)
                    {
                        // Extract scope directly from the pointee line
                        std::regex scopeRegex(R"(\s*->\s*(?:([a-zA-Z_][\w\.]*):\s+)?)");
                        std::smatch scopeMatch;
                        std::string scope = func; // Fallback to current function
                        if (std::regex_search(line, scopeMatch, scopeRegex) && scopeMatch[1].matched) {
                            scope = scopeMatch.str(1);
                        }

                        if (std::regex_search(line, pointeeMatches, pointeePattern_malloc))
                        {
                            ScopedPointer sp = {"", pointeeMatches.str(1)};
                            if (std::find(pointsToSets[i].pointees.begin(), pointsToSets[i].pointees.end(), sp) == pointsToSets[i].pointees.end())
                                pointsToSets[i].pointees.push_back(sp);
                        }
                        else if (std::regex_search(line, pointeeMatches, pointeePattern_alloca) ||
                                std::regex_search(line, pointeeMatches, pointeePattern_array) ||
                                std::regex_search(line, pointeeMatches, pointeePattern_variable))
                        {
                            ScopedPointer sp = {scope, pointeeMatches.str(1)};
                            if (std::find(pointsToSets[i].pointees.begin(), pointsToSets[i].pointees.end(), sp) == pointsToSets[i].pointees.end())
                                pointsToSets[i].pointees.push_back(sp);
                        }
                        else if (std::regex_search(line, pointeeMatches, pointeePattern_newLine))
                        {
                            ScopedPointer sp = {"", pointeeMatches.str(1)};
                            if (std::find(pointsToSets[i].pointees.begin(), pointsToSets[i].pointees.end(), sp) == pointsToSets[i].pointees.end())
                                pointsToSets[i].pointees.push_back(sp);
                        }
                        else if (std::regex_search(line, pointeeMatches, pointeePattern_null))
                        {
                            ScopedPointer sp = {"", "null"};
                            if (std::find(pointsToSets[i].pointees.begin(), pointsToSets[i].pointees.end(), sp) == pointsToSets[i].pointees.end())
                                pointsToSets[i].pointees.push_back(sp);
                        }
                        else
                        {
                            break;
                        }
                    }
                }
                tempFile = pointerMatches.suffix().str();
            }
        }
    }
}

void PointsToAnalysis::UnifyAssignmentEquivalenceClasses()
{
    std::istringstream flowStream(pointsToSetsBuffer.str());
    std::string flowLine;
    std::map<std::string, std::map<std::string, std::string>> localFlowMap;

    std::regex storeFlowRegex(R"(NODE\s+\d+:\s+([a-zA-Z_][\w\.]*):\s+store\s+.+?\s+[%@]([\w\.]+),\s*.+?\s+[%@]([\w\.]+))");
    std::regex loadFlowRegex(R"(NODE\s+\d+:\s+([a-zA-Z_][\w\.]*):\s+[%@]([\w\.]+)\s*=\s*load\s+.+?,\s*.+?\s+[%@]([\w\.]*))");

    while (std::getline(flowStream, flowLine))
    {
        std::smatch m;
        if (std::regex_search(flowLine, m, loadFlowRegex))
        {
            std::string func = m.str(1);
            std::string destReg = m.str(2);
            std::string srcVar = m.str(3);
            localFlowMap[func][destReg] = srcVar;
        }
        else if (std::regex_search(flowLine, m, storeFlowRegex))
        {
            std::string func = m.str(1);
            std::string srcOp = m.str(2);
            std::string destVar = m.str(3);

            std::string realSrc = srcOp;
            bool isLoadCopied = false;

            if (localFlowMap[func].count(srcOp))
            {
                realSrc = localFlowMap[func][srcOp];
                isLoadCopied = true;
            }

            // Direct pointer assignment detected: destVar = realSrc
            if (isLoadCopied)
            {
                ScopedPointer srcSp = {func, realSrc};
                ScopedPointer destSp = {func, destVar};

                int srcIdx = -1, destIdx = -1;
                for (size_t i = 0; i < pointsToSets.size(); ++i)
                {
                    if (std::find(pointsToSets[i].pointers.begin(), pointsToSets[i].pointers.end(), srcSp) != pointsToSets[i].pointers.end()) {
                        srcIdx = i;
                    }
                    if (std::find(pointsToSets[i].pointers.begin(), pointsToSets[i].pointers.end(), destSp) != pointsToSets[i].pointers.end()) {
                        destIdx = i;
                    }
                }

                // Unify the two equivalence classes if they are currently distinct
                if (srcIdx != -1 && destIdx != -1 && srcIdx != destIdx)
                {
                    // Unify pointer variables
                    for (const auto &ptr : pointsToSets[destIdx].pointers) {
                        if (std::find(pointsToSets[srcIdx].pointers.begin(), pointsToSets[srcIdx].pointers.end(), ptr) == pointsToSets[srcIdx].pointers.end()) {
                            pointsToSets[srcIdx].pointers.push_back(ptr);
                        }
                    }
                    // Unify extracted pointees
                    for (const auto &pte : pointsToSets[destIdx].pointees) {
                        if (std::find(pointsToSets[srcIdx].pointees.begin(), pointsToSets[srcIdx].pointees.end(), pte) == pointsToSets[srcIdx].pointees.end()) {
                            pointsToSets[srcIdx].pointees.push_back(pte);
                        }
                    }
                    // Erase the now redundant duplicate set
                    pointsToSets.erase(pointsToSets.begin() + destIdx);
                }
            }
        }
    }
}

void PointsToAnalysis::UnifyFunctionArgsEquivalenceClasses()
{
    std::istringstream flowStream(pointsToSetsBuffer.str());
    std::string flowLine;

    // Maps to track local variable dependencies and function signatures
    std::map<std::string, std::map<std::string, std::string>> localFlowMap;
    std::map<std::string, std::vector<std::string>> formalArgsMap;
    std::map<std::string, std::map<std::string, std::string>> paramStoreMap;

    std::regex storeFlowRegex(R"(NODE\s+\d+:\s+([a-zA-Z_][\w\.]*):\s+store\s+.+?\s+[%@]([\w\.]+),\s*.+?\s+[%@]([\w\.]+))");
    std::regex loadFlowRegex(R"(NODE\s+\d+:\s+([a-zA-Z_][\w\.]*):\s+[%@]([\w\.]+)\s*=\s*load\s+.+?,\s*.+?\s+[%@]([\w\.]*))");
    std::regex callFlowRegex(R"(NODE\s+\d+:\s+([a-zA-Z_][\w\.]*):\s+(?:[%@][\w\.]+\s*=\s*)?call\s+.+?@([a-zA-Z_][\w\.]*)\((.*)\))");

    // Phase 1: Build local flow maps and discover ordered formal parameters in callees
    while (std::getline(flowStream, flowLine))
    {
        std::smatch m;
        if (std::regex_search(flowLine, m, loadFlowRegex))
        {
            std::string func = m.str(1);
            std::string destReg = m.str(2);
            std::string srcVar = m.str(3);
            localFlowMap[func][destReg] = srcVar;
        }
        else if (std::regex_search(flowLine, m, storeFlowRegex))
        {
            std::string func = m.str(1);
            std::string srcOp = m.str(2);
            std::string destVar = m.str(3);

            // If a source operand is not loaded from within this function, it represents an incoming formal parameter
            if (localFlowMap[func].count(srcOp) == 0)
            {
                if (std::find(formalArgsMap[func].begin(), formalArgsMap[func].end(), srcOp) == formalArgsMap[func].end())
                {
                    formalArgsMap[func].push_back(srcOp);
                }
                paramStoreMap[func][srcOp] = destVar;
            }
        }
    }

    // Phase 2: Parse call statements and unify matching argument/parameter equivalence sets
    flowStream.clear();
    flowStream.seekg(0);

    while (std::getline(flowStream, flowLine))
    {
        std::smatch m;
        if (std::regex_search(flowLine, m, callFlowRegex))
        {
            std::string callerFunc = m.str(1);
            std::string calleeFunc = m.str(2);
            std::string argsStr = m.str(3);

            // Extract all actual argument registers from the call parameters
            std::vector<std::string> actualArgs;
            std::regex argReg(R"([%@]([\w\.]+))");
            auto arg_begin = std::sregex_iterator(argsStr.begin(), argsStr.end(), argReg);
            auto arg_end = std::sregex_iterator();
            for (std::sregex_iterator it = arg_begin; it != arg_end; ++it)
            {
                actualArgs.push_back((*it).str(1));
            }

            // Sync actual arguments from the caller to formal parameters in the callee by index
            for (size_t k = 0; k < actualArgs.size(); ++k)
            {
                if (k >= formalArgsMap[calleeFunc].size()) break;

                std::string actualReg = actualArgs[k];
                std::string formalArg = formalArgsMap[calleeFunc][k];

                // Resolve the temporary caller register back to its true source variable name
                std::string resolvedActual = actualReg;
                if (localFlowMap[callerFunc].count(actualReg))
                {
                    resolvedActual = localFlowMap[callerFunc][actualReg];
                }

                std::string formalAddr = "";
                if (paramStoreMap[calleeFunc].count(formalArg))
                {
                    formalAddr = paramStoreMap[calleeFunc][formalArg];
                }

                // Construct ScopedPointers to scan pointsToSets
                ScopedPointer callerSp = {callerFunc, resolvedActual};
                ScopedPointer calleeSp = {calleeFunc, formalArg};
                ScopedPointer calleeAddrSp = {calleeFunc, formalAddr};

                int callerIdx = -1, calleeIdx = -1, calleeAddrIdx = -1;
                for (size_t i = 0; i < pointsToSets.size(); ++i)
                {
                    if (std::find(pointsToSets[i].pointers.begin(), pointsToSets[i].pointers.end(), callerSp) != pointsToSets[i].pointers.end()) {
                        callerIdx = i;
                    }
                    if (std::find(pointsToSets[i].pointers.begin(), pointsToSets[i].pointers.end(), calleeSp) != pointsToSets[i].pointers.end()) {
                        calleeIdx = i;
                    }
                    if (!formalAddr.empty() && std::find(pointsToSets[i].pointers.begin(), pointsToSets[i].pointers.end(), calleeAddrSp) != pointsToSets[i].pointers.end()) {
                        calleeAddrIdx = i;
                    }
                }

                // Type Safety & Pointer Level Check: Only merge if data types and pointer levels match exactly
                if (callerIdx != -1 && calleeIdx != -1 && callerIdx != calleeIdx)
                {
                    if (pointsToSets[callerIdx].dataType == pointsToSets[calleeIdx].dataType)
                    {
                        for (const auto &ptr : pointsToSets[calleeIdx].pointers) {
                            if (std::find(pointsToSets[callerIdx].pointers.begin(), pointsToSets[callerIdx].pointers.end(), ptr) == pointsToSets[callerIdx].pointers.end()) {
                                pointsToSets[callerIdx].pointers.push_back(ptr);
                            }
                        }
                        for (const auto &pte : pointsToSets[calleeIdx].pointees) {
                            if (std::find(pointsToSets[callerIdx].pointees.begin(), pointsToSets[callerIdx].pointees.end(), pte) == pointsToSets[callerIdx].pointees.end()) {
                                pointsToSets[callerIdx].pointees.push_back(pte);
                            }
                        }
                        pointsToSets.erase(pointsToSets.begin() + calleeIdx);

                        // Shift tracking indexes if needed due to vector element erasure
                        if (calleeAddrIdx > calleeIdx) calleeAddrIdx--;
                        else if (calleeAddrIdx == calleeIdx) calleeAddrIdx = -1;
                        calleeIdx = -1;
                    }
                }

                // Unify the local parameter address variable (e.g., s1.addr) if type checks pass
                if (callerIdx != -1 && calleeAddrIdx != -1 && callerIdx != calleeAddrIdx)
                {
                    if (pointsToSets[callerIdx].dataType == pointsToSets[calleeAddrIdx].dataType)
                    {
                        for (const auto &ptr : pointsToSets[calleeAddrIdx].pointers) {
                            if (std::find(pointsToSets[callerIdx].pointers.begin(), pointsToSets[callerIdx].pointers.end(), ptr) == pointsToSets[callerIdx].pointers.end()) {
                                pointsToSets[callerIdx].pointers.push_back(ptr);
                            }
                        }
                        for (const auto &pte : pointsToSets[calleeAddrIdx].pointees) {
                            if (std::find(pointsToSets[callerIdx].pointees.begin(), pointsToSets[callerIdx].pointees.end(), pte) == pointsToSets[callerIdx].pointees.end()) {
                                pointsToSets[callerIdx].pointees.push_back(pte);
                            }
                        }
                        pointsToSets.erase(pointsToSets.begin() + calleeAddrIdx);
                    }
                }
            }
        }
    }
}


void PointsToAnalysis::ConstructPointsToSets()
{

    // A simple map: FunctionName -> VariableName -> Pointees
    std::map<std::string, std::map<std::string, std::vector<ScopedPointer>>> baseMap;

    // Step 1: Collect direct points-to relations using inline function prefixes
    CollectBasePointsTo(baseMap);

    // Step 2: Propagate complex relations via store and load instructions
    ResolveStoresAndLoads(baseMap);

    // Step 3: Track uninitialized pointer data-flow (Separated into a dedicated function)
    UnifyAssignmentEquivalenceClasses();

    // Step 4: Unify equivalence classes based on pointer assignments
    UnifyFunctionArgsEquivalenceClasses();
}

// escaped LLVM IR string literals (e.g., "\0A123\00") to their actual content (e.g., "\n123\0")
std::string PointsToAnalysis::decodeLLVMString(const std::string& input) {
    std::string result;
    for (size_t i = 0; i < input.length(); ++i) {
        if (input[i] == '\\' && i + 2 < input.length()) {
            // Extract the next two characters as a hexadecimal number
            std::string hex = input.substr(i + 1, 2);
            char ch = static_cast<char>(std::stoul(hex, nullptr, 16));
            result += ch;
            i += 2;
        } else {
            result += input[i];
        }
    }
    return result;
}

// Construct the list of string literals in the source code based on the points-to sets generated by DG.
void PointsToAnalysis::ConstructPointsToStrings()
{
    std::istringstream stream(pointsToSetsBuffer.str());
    std::string line;
    std::smatch matches;

    // Clarify the name of the pattern for parsing string literals
    std::regex stringLiteralRegex(R"(NODE\s+\d+:\s+(@\.str[\.\w]*) = .*c\\\"(.+?)\\\"\,\s*align.*)");

    int stringLiteralCount = 0;

    while (std::getline(stream, line))
    {
        if (std::regex_search(line, matches, stringLiteralRegex))
        {
            std::string llvmVarName = matches.str(1);    // e.g., "@.str"
            std::string rawHexContent = matches.str(2);  // e.g., "\0A\00"

            // Generate a unique C-style variable name for the converted output
            std::string convertedName = "str_lit_" + std::to_string(stringLiteralCount++);
            std::string decodedContent = decodeLLVMString(rawHexContent);

            // Save the mapped string literal info
            pointsToStrings.push_back({llvmVarName, convertedName, decodedContent});
        }
    }
}