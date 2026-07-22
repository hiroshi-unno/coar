#ifndef FILE_WRITER_H
#define FILE_WRITER_H

#include <string>
#include <fstream>
#include <iostream>

#include "info.h"

void WriteToFile(const std::string& content);
void WriteToAllocatedMemoryFile(const std::string& content);

#endif //FILE_WRITER_H