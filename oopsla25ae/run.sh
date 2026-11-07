#!/bin/bash
# Runs the tool on every benchmark of the paper's Section 7 (benchmarks/OCaml/oopsla25/*.ml),
# one at a time and without a time limit, and prints one CSV row per file,
# `file,verdict,seconds,iterations`, sorted; each run's full output is kept in
# oopsla25_logs/NAME.log at the repository root.
#
# The run is effcaml_nolimit of corpus oopsla25ae in script/bench_runs.txt (the input glob,
# the configuration, limit 0 = none), run by script/run_corpus.sh through the shared runner
# script/run_bench.sh from the repository root, where HorSat2 is expected as ./horsat2.
# The environment variables `timeout` and `para` override the limit and the parallelism.
set -u
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." || exit 2
shopt -s nullglob
files=(./benchmarks/OCaml/oopsla25/*.ml)
if (( ${#files[@]} == 0 )); then
    echo "No OOPSLA benchmarks found in ./benchmarks/OCaml/oopsla25" >&2
    exit 1
fi
export logdir=oopsla25_logs
exec ./script/run_corpus.sh oopsla25ae effcaml_nolimit
