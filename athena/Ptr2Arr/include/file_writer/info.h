#ifndef INFO_H
#define INFO_H

#include <filesystem>
#include <string>

extern std::string sourceCodeName;
extern std::filesystem::path outputDirectory;
extern std::filesystem::path outputSourcePath;
extern std::filesystem::path outputBitcodePath;
extern std::filesystem::path outputPointsToSetsPath;
extern std::filesystem::path outputMetadataPath;
extern std::filesystem::path outputAllocatedMemoryPath;
extern std::filesystem::path executableDirectory;

#endif //INFO_H