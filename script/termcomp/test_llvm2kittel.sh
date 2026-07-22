#! /bin/bash

# Test script for llvm2kittel in Docker container

# test_c_filepath="/root/coar/benchmarks/term-comp/C/AProVE_numeric/svcomp_gcd01_true-unreach-call_true-termination_modified.c"
test_c_filepath="/root/coar/benchmarks/term-comp/C/SV-COMP_Mixed_Categories/sum_non_eq_false-unreach-call.c"
base_name=$(basename $test_c_filepath ".c")

export PATH="/opt/llvm-3.6.2/bin:$PATH"

Ptr2Arr ${test_c_filepath}
clang -Wall -Wextra -c -emit-llvm -O0 ${base_name}_Ptr2Arr.c -o ${base_name}_Ptr2Arr.bc
opt -mem2reg -tailcallelim ${base_name}_Ptr2Arr.bc -o ${base_name}_tailcallelim.bc
llvm2kittel --dump-ll --no-slicing --eager-inline --t2 ${base_name}_tailcallelim.bc > ${base_name}_llvm2kittel.t2
echo "output of llvm2kittel (tail):"
tail ${base_name}_llvm2kittel.t2

output_t2_dir=$(pwd)
echo "solve using MuVal:"
cd /opt/coar && coar -c "/opt/coar/config/solver/muval_term_comp_parallel_exc_tbq_ar.json" -p "ltsterm" "$output_t2_dir/${base_name}_llvm2kittel.t2"