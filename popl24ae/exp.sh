#!/bin/bash
set -euo pipefail

timeout=600 # time limit in seconds
para=4 # the number of parallel executions
memlimit=256 # memory limit in GB

if [[ ! "$timeout" =~ ^[+]?([0-9]+([.][0-9]*)?|[.][0-9]+)([eE][+-]?[0-9]+)?[smhd]?$ ]] ||
        [[ ! "$para" =~ ^[0-9]+$ ]]; then
    echo "invalid timeout or parallelism setting" >&2
    exit 2
fi

artifact_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd -- "$artifact_dir/.."
staging=$(mktemp -d "$artifact_dir/.evaluation.XXXXXX")
trap 'status=$?; if [ "$status" -ne 0 ]; then echo "evaluation failed; unpublished results retained in $staging" >&2; fi' EXIT
python3 "$artifact_dir/evaluation_inputs.py" prepare "$artifact_dir" "$staging" "$memlimit"

for arm in spacer pcsat cps; do
    paths=()
    while IFS= read -r -d '' path; do paths+=("$path"); done < "$staging/$arm.paths"
    output="$staging/results_$arm.csv"
    if [ "$arm" = pcsat ]; then
        config=./config/solver/rcaml.json
    else
        config=./config/solver/rcaml_wopp_spacer.json
    fi
    if [ "${#paths[@]}" -gt 0 ]; then
        timeout=$timeout options="-c $config -p ml" para=$para \
            ./script/run_bench.sh "${paths[@]}" > "$output"
    else
        : > "$output"
    fi
    cat "$staging/$arm.excluded" >> "$output"
done

python3 "$artifact_dir/evaluation_inputs.py" validate "$artifact_dir" "$staging"
# All families validate before any publication. Each rename is atomic; the
# three replacements together are not a filesystem transaction.
for arm in spacer pcsat cps; do
    mv -f -- "$staging/results_$arm.csv" "$artifact_dir/results_$arm.csv"
done
rm -rf -- "$staging"
