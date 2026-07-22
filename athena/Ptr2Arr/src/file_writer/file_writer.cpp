#include "../../include/file_writer/file_writer.h"
#include <string.h>

void WriteToFile(const std::string& content) {
    const std::string outPath = outputMetadataPath;
    std::ofstream outFile(outPath, std::ios::app);
    if (!outFile) {
        std::cerr << strerror(errno) << ": " << outPath << std::endl;
        return;
    }
    outFile << content << std::endl;
    outFile.close();
}

void WriteToAllocatedMemoryFile(const std::string& content) {
    const std::string outPath = outputAllocatedMemoryPath;
    std::ofstream outFile(outPath, std::ios::app);
    if (!outFile) {
        std::cerr << strerror(errno) << ": " << outPath << std::endl;
        return;
    }
    outFile << content << std::endl;
    outFile.close();
}