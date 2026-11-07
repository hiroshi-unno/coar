#!/bin/bash
# Runs the paper's experiment with one strategy over TPDB's C_Integer inputs (Stroeder_15
# and Ton_Chanh_15, 335 files), 300 s each, and prints one CSV row per input,
# `file,answer,seconds[,iterations]`, sorted.
#
#   run.sh eager|lazy
#
# The run is dt_<strategy>_300 of corpus cav21ae_dt in script/bench_runs.txt (the prove and
# the disprove configuration of the strategy, the limit, the input globs), run by
# script/run_corpus.sh from the repository root through prove_disprove_bench.sh beside this
# script.  The environment variable `timeout` overrides the limit.
set -u
case ${1-} in
eager | lazy) ;;
*)
	echo "usage: $0 eager|lazy" >&2
	exit 2
	;;
esac
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." || exit 2
exec ./script/run_corpus.sh cav21ae_dt "dt_$1_300"
