#!/usr/bin/env bash
# Runs one solver of CoAR's CHC-COMP 2025 entry over the competition tracks, one track at a
# time, through run_bench.sh beside this script (which maps a track's `.set` file under
# benchmarks/chc-comp25/ to its inputs and calls the repository's runner).  Written for the
# container compose.yaml starts: the tool is /root/coar/main.exe and the working directory
# the repository root, which the configuration paths below are relative to.
#
#   run_tracks.sh SOLVER     SOLVER is `pcsat` or `mucyc`
#
# Each solver is a label, a configuration and a list of tracks; the limit (300 s), the
# parallelism (6) and the binary are shared.  Results go to
# bench_results/<label>_<start time>/ beside this script: per track <track>_<time>.csv (the
# runner's CSV), <track>_<time>_error.log (its stderr) and <track>_<time>_sorted.csv (the CSV
# sorted case-insensitively).  run_bench_pcsat.sh and run_bench_mucyc.sh are this script
# with the argument fixed, kept under the names the competition notes use.

# strict mode
set -euo pipefail
IFS=$'\n\t'

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

case "${1-}" in
pcsat)
	solver='pcsat-tbp-ar'
	options='-c ./config/solver/pcsat_verdict_only.json -p pcsp'
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
	;;
mucyc)
	solver='mucyc-returnF-mbp0-indNF'
	options='-c ./config/solver/mucyc_returnF_mbp0_indNF.json -p pcsp'
	# MuCyc entered the two LIA tracks only.
	TRACKS=(
		'LIA'
		'LIA-Lin'
	)
	;;
*)
	echo "usage: $0 pcsat|mucyc" >&2
	exit 2
	;;
esac
[ "$#" -eq 1 ] || { echo "usage: $0 pcsat|mucyc" >&2; exit 2; }

export options
export cmd="/root/coar/main.exe"
export para=6
export timeout=300

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
