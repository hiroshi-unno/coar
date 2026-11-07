#!/bin/bash
# Builds the tool, then runs it over a corpus with script/run_bench.sh, eight runs at a
# time and no restart: `timeout=10 options='-c CONFIG -p P' script/bench.sh PATHS...`.
[ -n "${timeout-}" ] || { echo "e.g., timeout=10 ... $0" >&2; exit 2; }
[ -n "${options-}" ] || { echo "e.g., options='-c ./config/solver/pcsat.json -p pcsp' ... $0" >&2; exit 2; }
dune build main.exe || exit 1
exec env para=8 retries=0 cmd=_build/default/main.exe "$(dirname -- "$0")/run_bench.sh" "$@"
