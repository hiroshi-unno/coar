cmake_minimum_required(VERSION 3.27)
project(TypeAnnotator)

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

add_executable(TypeAnnotator
        src/main.cpp

        include/info.h
        src/info.cpp

        include/bit_operation_visitor/bit_operation_action.h
        src/bit_operation_visitor/bit_operation_action.cpp
        include/bit_operation_visitor/bit_operation_consumer.h
        src/bit_operation_visitor/bit_operation_consumer.cpp
        include/bit_operation_visitor/bit_operation_visitor.h
        src/bit_operation_visitor/bit_operation_visitor.cpp

        include/bit_variable_visitor/bit_variable.h
        include/bit_variable_visitor/bit_variable_action.h
        src/bit_variable_visitor/bit_variable_action.cpp
        include/bit_variable_visitor/bit_variable_consumer.h
        src/bit_variable_visitor/bit_variable_consumer.cpp
        include/bit_variable_visitor/bit_variable_visitor.h
        src/bit_variable_visitor/bit_variable_visitor.cpp

        include/nondet_variable_visitor/nondet_variable.h
        include/nondet_variable_visitor/nondet_variable_action.h
        src/nondet_variable_visitor/nondet_variable_action.cpp
        include/nondet_variable_visitor/nondet_variable_consumer.h
        src/nondet_variable_visitor/nondet_variable_consumer.cpp
        include/nondet_variable_visitor/nondet_variable_visitor.h
        src/nondet_variable_visitor/nondet_variable_visitor.cpp
)

# Link against specific LLVM and Clang libraries
target_link_libraries(TypeAnnotator
        LLVM
        clangAST
        clangFrontend
        clangTooling
)