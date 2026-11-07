#! /bin/bash
# Runs MuCyc over the CHC-COMP 2024 LIA-Lin and LIA tracks (the runs chc24lialin mucyc_600
# and chc24lianolin mucyc_600 of the run table) and keeps each run's output, stderr included,
# as script/<corpus>/mucyc.csv.  The runs expand their input globs in the working directory,
# so this changes to the repository root first and works from any directory.
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." || exit 2
script/chc24lialin/mucyc_600.sh |& tee script/chc24lialin/mucyc.csv
script/chc24lianolin/mucyc_600.sh |& tee script/chc24lianolin/mucyc.csv
