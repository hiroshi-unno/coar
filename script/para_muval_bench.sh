#!/bin/bash
# Run script/para_muval.sh on every input file found under the given paths, one at a time.
SCRIPT_DIR=$(cd -- "$(dirname -- "$0")" && pwd) || exit 1
exec bash "$SCRIPT_DIR/run_parallel_muval_bench.sh" para_muval.sh "$@"
