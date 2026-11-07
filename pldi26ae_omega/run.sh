#!/bin/bash
# Runs the nine omega-regular benchmarks under each of the five certificate kinds of the
# paper (LexPMSM, LexGSSM, PMSM, GSSM, SSM), 180 s each, one at a time.  Writes, at the
# repository root, results/pldi26ae_omega/<kind>.csv (rows `file,verdict,seconds,iterations`,
# sorted) and keeps each run's full output in results/pldi26ae_omega/logs/<kind>/NAME.log;
# prints every row to standard output under a heading per kind.  Run it with PolyQEnt's
# virtual environment active.
#
# Each kind is a run of corpus pldi26ae_omega in script/bench_runs.txt (the files, the
# configuration file, the 180 s limit), run by script/run_corpus.sh through the shared
# runner script/run_bench.sh from the repository root.  The environment variables `timeout`
# and `para` override the limit and the parallelism.  Exit status: the first failing run's.
set -u
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." || exit 2
out=results/pldi26ae_omega
mkdir -p -- "$out" || exit 2
status=0
for pair in LexPMSM:lexpmsm LexGSSM:lexgssm PMSM:pmsm GSSM:gssm SSM:ssm; do
	label=${pair%%:*} run=muval_qfl_omega_${pair#*:}_polyqent_deg1_180
	echo "=============== $label ==============="
	if logdir=$out/logs/$label ./script/run_corpus.sh pldi26ae_omega "$run" >"$out/$label.csv.tmp"; then
		mv -f -- "$out/$label.csv.tmp" "$out/$label.csv"
		cat -- "$out/$label.csv"
	else
		rc=$?
		echo "run $run failed (status $rc); partial rows kept in $out/$label.csv.tmp" >&2
		[ "$status" -eq 0 ] && status=$rc
	fi
	echo
done
exit "$status"
