#!/usr/bin/env bash
set -e

artifact_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd -- "$artifact_dir/.."

python3 "$artifact_dir/summarize_results.py" --prepare-plots "$PWD"

mkdir -p results/comparison results/fig

gnuplot "$artifact_dir"/fig/1a/pr_vs_dwf_popl23.plt

gnuplot "$artifact_dir"/fig/1a/pr_vs_dwf_its.plt

gnuplot "$artifact_dir"/fig/1b/pr_vs_wf_popl23.plt

gnuplot "$artifact_dir"/fig/1b/pr_vs_wf_its.plt

gnuplot "$artifact_dir"/fig/2a/pr_vs_wo_scc_popl23.plt

gnuplot "$artifact_dir"/fig/2a/pr_vs_wo_scc_its.plt

gnuplot "$artifact_dir"/fig/2b/pr_vs_wo_ad_popl23.plt

gnuplot "$artifact_dir"/fig/2b/pr_vs_wo_ad_its.plt


gnuplot "$artifact_dir"/fig/2c/pr_vs_wo_ad_scc_popl23.plt

gnuplot "$artifact_dir"/fig/2c/pr_vs_wo_ad_scc_its.plt

