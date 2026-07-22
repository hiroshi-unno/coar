cmake_minimum_required(VERSION 3.27)
project(Ptr2Arr)

# Set the C++ standard to C++23
set(CMAKE_CXX_STANDARD 23)

# Find LLVM package
find_package(LLVM REQUIRED CONFIG COMPONENTS)
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

# Add Clang's resource directory to the include paths to find standard headers like 'stddef.h'
find_program(CLANG_EXECUTABLE clang)
if (CLANG_EXECUTABLE)
    execute_process(COMMAND ${CLANG_EXECUTABLE} -print-resource-dir OUTPUT_VARIABLE CLANG_RESOURCE_DIR)
    string(STRIP ${CLANG_RESOURCE_DIR} CLANG_RESOURCE_DIR_STRIPPED)
    include_directories(SYSTEM ${CLANG_RESOURCE_DIR_STRIPPED}/include)
endif()

add_executable(Ptr2Arr
        src/main.cpp

        include/pointer_visitor/pointer_action.h
        src/pointer_visitor/pointer_action.cpp
        include/pointer_visitor/pointer_consumer.h
        src/pointer_visitor/pointer_consumer.cpp
        include/pointer_visitor/pointer_visitor.h
        src/pointer_visitor/pointer_visitor.cpp

        include/points_to_analysis/points_to_set.h
        include/points_to_analysis/points_to_analysis.h
        src/points_to_analysis/points_to_analysis.cpp

        include/memory_analysis/memory_set.h
        src/memory_analysis/memory_analysis.cpp
        include/memory_analysis/memory_analysis.h

        include/code_visitor_and_rewriter/tracking_rewriter.h
        src/code_visitor_and_rewriter/tracking_rewriter.cpp
        include/code_visitor_and_rewriter/code_action.h
        src/code_visitor_and_rewriter/code_action.cpp
        include/code_visitor_and_rewriter/code_consumer.h
        src/code_visitor_and_rewriter/code_consumer.cpp
        include/code_visitor_and_rewriter/code_visitor_and_rewriter.h
        src/code_visitor_and_rewriter/code_visitor_and_rewriter.cpp

        include/bit_expression_visitor_and_rewriter/bit_expression_action.h
        src/bit_expression_visitor_and_rewriter/bit_expression_action.cpp
        include/bit_expression_visitor_and_rewriter/bit_expression_consumer.h
        src/bit_expression_visitor_and_rewriter/bit_expression_consumer.cpp
        include/bit_expression_visitor_and_rewriter/bit_expression_visitor_and_rewriter.h
        src/bit_expression_visitor_and_rewriter/bit_expression_visitor_and_rewriter.cpp

        include/file_writer/info.h
        src/file_writer/info.cpp
        include/file_writer/file_writer.h
        src/file_writer/file_writer.cpp

        include/llvm_var_analysis/llvm_var_analysis.h
        src/llvm_var_analysis/llvm_var_analysis.cpp
)

# Link against specific LLVM and Clang libraries
target_link_libraries(Ptr2Arr
        LLVM
        clangAST
        clangFrontend
        clangTooling
        -lstdc++
)