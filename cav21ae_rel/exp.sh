#!/bin/bash
# Runs every file of Table 1 under the default configuration (config/solver/pcsat.json),
# 1200 s each, one at a time: the plain files, and the *_hint files the paper ran in their
# place (kept for comparison).  Neither the hints nor hand-chosen template parameters are
# needed any longer; see README.md.
#
# The run is pcsat_1200 of corpus cav21ae_rel in script/bench_runs.txt (the file list, the
# configuration and the limit), run by script/run_corpus.sh through the shared runner
# script/run_bench.sh from the repository root.  It prints one CSV row per file,
# `file,verdict,seconds,iterations`, sorted; progress goes to standard error.  The
# environment variables `timeout` and `para` override the limit and the parallelism.
set -u
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." || exit 2
exec ./script/run_corpus.sh cav21ae_rel pcsat_1200
