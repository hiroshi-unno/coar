#!/bin/bash
# The corpus loop of this package: races the prove and the disprove configuration on each C
# input in turn (para_muval_prove_disprove.sh beside this script: clang and llvm2kittel
# translate the input to T2, both configurations run on it, the first to finish is reported)
# and prints one CSV row per input, `file,answer,seconds[,iterations]`.
#
#   timeout=T prove_config=C1 disprove_config=C2 options='-p ltsterm' prove_disprove_bench.sh FILE...
#
# Run from the repository root (the driver names ./_build/default/main.exe and its helpers
# relative to it).  The rows of corpus cav21ae_dt in script/bench_runs.txt call it with the
# paper's configurations; to run a selection of inputs, call it directly with those files
# (`script/run_corpus.sh --dry-run cav21ae_dt dt_eager_300` prints a full call).  The
# drivers' own diagnostics are discarded, as in the paper's runs.
set -u
: "${timeout:?timeout unset}" "${prove_config:?prove_config unset}" "${disprove_config:?disprove_config unset}" "${options:?options unset}"
export timeout prove_config disprove_config options
here=$(dirname -- "${BASH_SOURCE[0]}")
for file in "$@"; do
	"$here/para_muval_prove_disprove.sh" "$file" 2>/dev/null
done
