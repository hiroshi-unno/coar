#!/bin/bash
# Reproduces Table 2: the 35 benchmarks, each under its configuration (the table's "Config"
# column: A, B, C1, C2, C3), 180 s each, one at a time.  Writes, at the repository root,
# results/pldi26ae_lower/<config>.csv (rows `file,verdict,seconds,iterations`, sorted) and
# keeps each run's full output (the verified bound and certificates) in
# results/pldi26ae_lower/logs/<config>/NAME.log; prints every row to standard output under a
# `Config X` heading.  Run it with PolyQEnt's virtual environment active.
#
# Each configuration is a run of corpus pldi26ae_lower in script/bench_runs.txt (its files,
# the configuration file, the 180 s limit), run by script/run_corpus.sh through the shared
# runner script/run_bench.sh from the repository root.  The environment variables `timeout`
# and `para` override the limit and the parallelism.  Exit status: the first failing run's.
set -u
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." || exit 2
out=results/pldi26ae_lower
mkdir -p -- "$out" || exit 2
status=0
for pair in A:muval_qfl_polyqent_deg3 B:muval_qfl_polyqent_deg1 C1:muval_qfl_polyqent_deg1_eps \
	C2:muval_qfl_polyqent_deg1_cond_eps C3:muval_qfl_polyqent_deg1_1_cond_eps; do
	label=${pair%%:*} config=${pair#*:}
	echo "Config $label ($config)"
	if logdir=$out/logs/$label ./script/run_corpus.sh pldi26ae_lower "${config}_180" >"$out/$label.csv.tmp"; then
		mv -f -- "$out/$label.csv.tmp" "$out/$label.csv"
		cat -- "$out/$label.csv"
	else
		rc=$?
		echo "run ${config}_180 failed (status $rc); partial rows kept in $out/$label.csv.tmp" >&2
		[ "$status" -eq 0 ] && status=$rc
	fi
	echo
done
exit "$status"
