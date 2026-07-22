#!/bin/bash

# strict mode
set -euo pipefail
IFS=$'\n\t'

solver='muval'
export timeout=300

SCRIPT_DIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)
REPO_ROOT_DIR="$SCRIPT_DIR/../.."

export options="-c $REPO_ROOT_DIR/config/solver/muval_parallel_exc_tbq_ar.json -p pltsterm"
# export options="-c $REPO_ROOT_DIR/config/solver/muval_parallel_tbq_ar.json -p pltsterm"

# prepare a directory to store results (includes a timestamp in it's name)
TIMESTAMP=$(date +"%Y-%m-%d_%H-%M-%S")
RESULT_DIR="$SCRIPT_DIR/termcomp_bench_results"
mkdir -p $RESULT_DIR

BENCHMARKS_DIR="$REPO_ROOT_DIR/benchmarks/term-comp/Integer_Transition_Systems"


TRACKS=(
	"Integer_Transition_Systems"
)

for track in "${TRACKS[@]}"; do
	echo $track

    timestamp=$(date +"%Y-%m-%d_%H-%M-%S")
	result_filestem="${RESULT_DIR}/${track}_${solver}_${timestamp}"

    FULL_SMT2_PATHS=$(find "${BENCHMARKS_DIR}" -type f -name "*.smt2")
    # echo ${FULL_SMT2_PATHS[@]}

	${SCRIPT_DIR}/../run_bench.sh ${FULL_SMT2_PATHS[@]} > "${result_filestem}.csv" 2> "${result_filestem}_error.log"
	LC_ALL="C" sort "${result_filestem}.csv" > "${result_filestem}_sorted.csv"
done

