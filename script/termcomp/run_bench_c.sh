#!/bin/bash

# strict mode
set -euo pipefail
IFS=$'\n\t'

solver='muval'

SCRIPT_DIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)
REPO_ROOT_DIR="$SCRIPT_DIR/../.."

export options="--timeout=60 --category=C"
export cmd="solver"
export timeout=60
export para=6
# export options="-c $REPO_ROOT_DIR/config/solver/muval_parallel_tbq_ar.json -p pltsterm"

# prepare a directory to store results (includes a timestamp in it's name)
TIMESTAMP=$(date +"%Y-%m-%d_%H-%M-%S")
RESULT_DIR="$SCRIPT_DIR/termcomp_bench_results"
mkdir -p $RESULT_DIR

BENCHMARKS_DIR="$REPO_ROOT_DIR/benchmarks/term-comp/C/"


TRACKS=(
	"C"
)

for track in "${TRACKS[@]}"; do
	echo $track

    timestamp=$(date +"%Y-%m-%d_%H-%M-%S")
	result_filestem="${RESULT_DIR}/${track}_${solver}_${timestamp}"

    BENCH_C_PATHS=$(find "${BENCHMARKS_DIR}" -type f -name "*.c")
    # echo ${FULL_SMT2_PATHS[@]}

	${SCRIPT_DIR}/../run_bench.sh ${BENCH_C_PATHS[@]} > "${result_filestem}.csv" 2> "${result_filestem}_error.log"
	LC_ALL="C" sort -f "${result_filestem}.csv" > "${result_filestem}_sorted.csv"
done

