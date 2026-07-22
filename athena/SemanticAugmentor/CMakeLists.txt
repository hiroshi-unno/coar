cmake_minimum_required(VERSION 3.27)
project(SemanticAugmentor)

# Set the C++ standard to C++23
set(CMAKE_CXX_STANDARD 23)

# Find LLVM package
find_package(LLVM REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

# Include LLVM headers
include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

# Find Clang package
find_package(Clang REQUIRED CONFIG)
message(STATUS "Using ClangConfig.cmake in: ${CLANG_DIR}")

# Include Clang headers
include_directories(${CLANG_INCLUDE_DIRS})

add_executable(SemanticAugmentor
        src/main.cpp

        include/info.h
        src/info.cpp

        include/bit_operation_visitor/bit_operation_action.h
        src/bit_operation_visitor/bit_operation_action.cpp
        include/bit_operation_visitor/bit_operation_consumer.h
        src/bit_operation_visitor/bit_operation_consumer.cpp
        include/bit_operation_visitor/bit_operation_visitor.h
        src/bit_operation_visitor/bit_operation_visitor.cpp

        include/data_parser/data.h
        include/data_parser/data_parser.h
        src/data_parser/data_parser.cpp

        include/brace_visitor_and_rewriter/brace_action.h
        src/brace_visitor_and_rewriter/brace_action.cpp
        include/brace_visitor_and_rewriter/brace_consumer.h
        src/brace_visitor_and_rewriter/brace_consumer.cpp
        include/brace_visitor_and_rewriter/brace_visitor_and_rewriter.h
        src/brace_visitor_and_rewriter/brace_visitor_and_rewriter.cpp

        include/code_visitor_and_rewriter/code_action.h
        src/code_visitor_and_rewriter/code_action.cpp
        include/code_visitor_and_rewriter/code_consumer.h
        src/code_visitor_and_rewriter/code_consumer.cpp
        include/code_visitor_and_rewriter/code_visitor_and_rewriter.h
        src/code_visitor_and_rewriter/code_visitor_and_rewriter.cpp
)

# Link against specific LLVM and Clang libraries
target_link_libraries(SemanticAugmentor
        LLVM
        clangAST
        clangFrontend
        clangTooling
)