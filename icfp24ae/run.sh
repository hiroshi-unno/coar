#!/bin/bash
# Runs the 14 programs of Table 2, 300 s each, one at a time, and writes the CSV
# `file,verdict,seconds,iterations` (sorted) to result.csv at the repository root, as well as to
# standard output; each run's full output (the inferred types) is kept in result_logs/NAME.log.
#
# Every program here is in an expectation mode, i.e. a quantitative lambda-HFL problem, and
# goes through MuValQHFL (-p qhfl), which types it with RCaml's default configuration and
# prints `valid` where RCaml prints `sat`.  MuValQHFL refuses a file without an expectation
# mode, so a program added to the run must carry one.
#
# The run is muval_qhfl_300 of corpus icfp24ae in script/bench_runs.txt (the file list, the
# configuration and the limit), run by script/run_corpus.sh through the shared runner
# script/run_bench.sh from the repository root.  The environment variables `timeout` and
# `para` override the limit and the parallelism.  Exit status: the run's (nonzero when the
# runner fails); result.csv is replaced only when the run completed.
set -u
set -o pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." || exit 2
export logdir=result_logs
./script/run_corpus.sh icfp24ae muval_qhfl_300 | tee result.csv.tmp
status=$?
[ "$status" -eq 0 ] && mv -f -- result.csv.tmp result.csv
exit "$status"
