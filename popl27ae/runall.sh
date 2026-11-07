#!/bin/bash

set -e
artifact_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd -- "$artifact_dir/.."
mkdir -p results
staging=$(mktemp -d results/.popl27-run.XXXXXX)
trap 'status=$?; if [ "$status" -ne 0 ]; then echo "evaluation failed; unpublished results retained in $staging" >&2; fi' EXIT
mkdir -p "$staging/popl2023mod" "$staging/term25its"

run_family() {
    local script=$1 output=$2
    "$script" > "$staging/$output"
    if [ ! -s "$staging/$output" ]; then
        echo "evaluation produced no rows: $script" >&2
        return 1
    fi
}

mkdir -p results/popl2023mod

# POPL23 benchmarks
echo
echo "=== POPL23 benchmarks - MuValPPM SCC & AD ==="
run_family ./script/popl2023mod/muval_ppm_popl27_300.sh popl2023mod/muval_ppm_popl27.csv

echo
echo "=== POPL23 benchmarks - MuValPPM AD ==="
run_family ./script/popl2023mod/muval_ppm_popl27_no_scc_300.sh popl2023mod/muval_ppm_popl27_no_scc.csv

echo
echo "=== POPL23 benchmarks - MuValPPM SCC ==="
run_family ./script/popl2023mod/muval_ppm_popl27_no_ad_300.sh popl2023mod/muval_ppm_popl27_no_ad.csv

echo
echo "=== POPL23 benchmarks - MuValPPM no optimization ==="
run_family ./script/popl2023mod/muval_ppm_popl27_no_scc_ad_300.sh popl2023mod/muval_ppm_popl27_no_scc_ad.csv

echo
echo "=== POPL23 benchmarks - MuVal [Unno et al. 2023] ==="
run_family ./script/popl2023mod/muval_popl27_300.sh popl2023mod/muval.csv

echo
echo "=== POPL23 benchmarks - MuStrat [Tsukada et al. 2025] ==="
run_family ./script/popl2023mod/mustrat_popl27_300.sh popl2023mod/mustrat.csv


mkdir -p results/term25its

# TermCOMP ITS benchmarks
echo
echo "=== TermCOMP ITS benchmarks - MuValPPM SCC & AD ==="
run_family ./script/term25its/muval_ppm_popl27_300.sh term25its/muval_ppm_popl27.csv

echo
echo "=== TermCOMP ITS benchmarks - MuValPPM AD ==="
run_family ./script/term25its/muval_ppm_popl27_no_scc_300.sh term25its/muval_ppm_popl27_no_scc.csv

echo
echo "=== TermCOMP ITS benchmarks - MuValPPM SCC ==="
run_family ./script/term25its/muval_ppm_popl27_no_ad_300.sh term25its/muval_ppm_popl27_no_ad.csv

echo
echo "=== TermCOMP ITS benchmarks - MuValPPM no optimization ==="
run_family ./script/term25its/muval_ppm_popl27_no_scc_ad_300.sh term25its/muval_ppm_popl27_no_scc_ad.csv

echo
echo "=== TermCOMP ITS benchmarks - MuVal [Unno et al. 2023] ==="
run_family ./script/term25its/muval_popl27_300.sh term25its/muval.csv

echo
echo "=== TermCOMP ITS benchmarks - MuStrat [Tsukada et al. 2025] ==="
run_family ./script/term25its/mustrat_popl27_300.sh term25its/mustrat.csv

# Check complete, matching benchmark identities before publishing either corpus.
python3 "$artifact_dir/summarize_results.py" --validate-times "$staging/popl2023mod"/*.csv >/dev/null
python3 "$artifact_dir/summarize_results.py" --validate-times "$staging/term25its"/*.csv >/dev/null

# Publish only after every family completed; failed runs retain their staging data.
for corpus in popl2023mod term25its; do
    for file in "$staging/$corpus"/*.csv; do
        mv -f -- "$file" "results/$corpus/"
    done
done
rmdir -- "$staging/popl2023mod" "$staging/term25its" "$staging"
