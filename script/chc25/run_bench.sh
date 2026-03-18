#!/usr/bin/env bash

# strict mode
set -euo pipefail
IFS=$'\n\t'

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

BENCHMARKS_DIR="${SCRIPT_DIR}/../benchmarks/chc-comp25"
PATHS_LIST_FILE="${BENCHMARKS_DIR}/$1.set"

# get array of .yml paths
mapfile -t YML_PATHS < $PATHS_LIST_FILE

# .yml -> .smt2
SMT2_PATHS=("${YML_PATHS[@]/%.yml/.smt2}")
FULL_SMT2_PATHS=("${SMT2_PATHS[@]/#/${BENCHMARKS_DIR}/}")

# echo "${FULL_SMT2_PATHS[@]}"
${SCRIPT_DIR}/run_bench.sh "${FULL_SMT2_PATHS[@]}"
