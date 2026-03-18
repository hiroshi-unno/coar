#!/usr/bin/env bash

# strict mode
set -euo pipefail
IFS=$'\n\t'

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

solver='mucyc-returnF-mbp0-indNF'
export timeout=300
export options='-c ./config/solver/mucyc_returnF_mbp0_indNF.json -p pcsp'

RESULT_DIR="$SCRIPT_DIR/chc25benchresults"

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

for track in "${TRACKS[@]}"; do
	echo $track
	timestamp=$(date +"%Y-%m-%d_%H-%M-%S")
	result_filestem="${RESULT_DIR}/${solver}_${track}_${timestamp}"
	${SCRIPT_DIR}/run_bench_chccomp2025.sh $track > "${result_filestem}.csv" 2> "${result_filestem}_error.log"
	LC_ALL="C" sort "${result_filestem}.csv" > "${result_filestem}_sorted.csv"
done
