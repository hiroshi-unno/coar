#!/bin/sh
set -eu
cd "$(dirname "$0")"
# Preparing the plot data prints one `<figure name> <seconds>` line per figure:
# the time limit the results' timeout rows record, at which the figure draws
# every timeout. Arguments (e.g. `--timeout 60` for results written by an older
# runner, whose timeout rows record no time) go to the preparation step.
limits=$(python3 prepare_plots.py LRA "$@")
echo "generating scatter plots for LRA"
printf '%s\n' "$limits" | while read -r name seconds; do
    gnuplot -e "TO=$seconds" "$name.plt"
done
