#!/usr/bin/env bash

# strict mode
set -euo pipefail
IFS=$'\n\t'

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

solver='pcsat-tbp-ar'
export timeout=300
export options='-c ./config/solver/pcsat_chc_comp_tbq_ar.json -p pcsp'

START_TIME=$(date +"%Y-%m-%d_%H-%M-%S")
RESULT_DIR="$SCRIPT_DIR/chc25benchresults/$START_TIME"

mkdir -p $RESULT_DIR

TRACKS=(
	'LIA'
	'LIA-Lin'
	'LRA-Lin'
	'BV'
	'LIA-Lin-Arrays'
	'LIA-Arrays'
	'ADT-LIA-Arrays'
	'ADT-LIA'
)

for track in "${TRACKS[@]}"; do
	echo $track
	timestamp=$(date +"%Y-%m-%d_%H-%M-%S")
	result_filestem="${RESULT_DIR}/${solver}_${track}_${timestamp}"
	${SCRIPT_DIR}/run_bench_chccomp2025.sh $track > "${result_filestem}.csv" 2> "${result_filestem}_error.log"
	LC_ALL="C" sort "${result_filestem}.csv" > "${result_filestem}_sorted.csv"
done
