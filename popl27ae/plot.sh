#!/usr/bin/env bash
set -e

artifact_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd -- "$artifact_dir/.."

# Preparing the plot data prints one `<figure data name> <seconds>` line per
# figure: the time limit the results' timeout rows record, at which the figure
# draws every timeout. Arguments (e.g. `--timeout 60` for results written by an
# older runner, whose timeout rows record no time) go to the preparation step.
limits=$(python3 "$artifact_dir/summarize_results.py" --prepare-plots "$PWD" "$@")
declare -A limit
while read -r name seconds; do
  limit[$name]=$seconds
done <<< "$limits"

mkdir -p results/comparison results/fig

plot() {
  gnuplot -e "TO=${limit[$1]:?no time limit prepared for $1}" "$artifact_dir/fig/$2/$1.plt"
}

plot pr_vs_dwf_popl23 1a
plot pr_vs_dwf_its 1a
plot pr_vs_wf_popl23 1b
plot pr_vs_wf_its 1b
plot pr_vs_wo_scc_popl23 2a
plot pr_vs_wo_scc_its 2a
plot pr_vs_wo_ad_popl23 2b
plot pr_vs_wo_ad_its 2b
plot pr_vs_wo_ad_scc_popl23 2c
plot pr_vs_wo_ad_scc_its 2c
