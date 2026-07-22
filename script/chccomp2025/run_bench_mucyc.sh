#!/usr/bin/env bash

# strict mode
set -euo pipefail
IFS=$'\n\t'

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

solver='mucyc-returnF-mbp0-indNF'
export options='-c ./config/solver/mucyc_chc_comp_returnF_mbp0_indNF.json -p pcsp'
export cmd="/root/coar/main.exe"
export para=6
export timeout=300

TRACKS=(
	'LIA'
	'LIA-Lin'
	# 'LRA-Lin'
	# 'BV'
	# 'LIA-Lin-Arrays'
	# 'LIA-Arrays'
	# 'ADT-LIA-Arrays'
	# 'ADT-LIA'
)

START_TIME=$(date +"%Y-%m-%d_%H-%M-%S")
RESULT_DIR="$SCRIPT_DIR/bench_results/${solver}_${START_TIME}"
mkdir -p "$RESULT_DIR"

for track in "${TRACKS[@]}"; do
	echo "Running: $track"
	timestamp=$(date +"%Y-%m-%d_%H-%M-%S")
	result_filestem="${RESULT_DIR}/${track}_${timestamp}"
	"${SCRIPT_DIR}/run_bench.sh" "$track" > "${result_filestem}.csv" 2> "${result_filestem}_error.log"
	LC_ALL="C" sort -f "${result_filestem}.csv" > "${result_filestem}_sorted.csv"
done
