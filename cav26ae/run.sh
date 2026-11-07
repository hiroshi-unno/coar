#!/bin/bash
# Runs this package's experiments for one logic and writes <LOGIC>_<arm>.csv beside this
# script, the files gen_figs_<LOGIC>.sh plots.
#
#   run.sh LIA|LRA [ARM...]     ARM: mucyc_qsat_deepest_own_projected_repeatedly (progress ensured),
#                               mucyc_qsat_deepest_own (Bjorner-Janota return), z3_smt (default: all three)
#
# Each arm is the run <LOGIC>_<arm>_300 of corpus cav26ae in script/bench_runs.txt (the
# configuration, the 300 s limit, one input at a time, the input globs), run by
# script/run_corpus.sh through the shared runner script/run_bench.sh from the repository
# root.  The environment variables `timeout` and `para` override the row's limit and
# parallelism.  A CSV replaces the previous one only when its run completed; the exit status
# is the first failing run's.
set -u
case ${1-} in
LIA | LRA) logic=$1 ;;
*)
	echo "usage: $0 LIA|LRA [mucyc_qsat_deepest_own_projected_repeatedly|mucyc_qsat_deepest_own|z3_smt ...]" >&2
	exit 2
	;;
esac
shift
arms=("$@")
[ ${#arms[@]} -gt 0 ] || arms=(mucyc_qsat_deepest_own_projected_repeatedly mucyc_qsat_deepest_own z3_smt)
artifact_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd) || exit 2
cd -- "$artifact_dir/.." || exit 2
status=0
for arm in "${arms[@]}"; do
	out=$artifact_dir/${logic}_$arm.csv
	echo "=== $logic $arm ===" >&2
	if ./script/run_corpus.sh cav26ae "${logic}_${arm}_300" >"$out.tmp"; then
		mv -f -- "$out.tmp" "$out"
	else
		rc=$?
		echo "run ${logic}_${arm}_300 failed (status $rc); partial rows kept in $out.tmp" >&2
		[ "$status" -eq 0 ] && status=$rc
	fi
done
exit "$status"
