#!/bin/bash

set -o pipefail

SCRIPT_DIR=$(
    cd $(dirname $0)/..
    pwd
)
timeout=300 options='-c ./config/solver/mustrat.json -p pltsterm ' para=4 $SCRIPT_DIR/run_bench.sh benchmarks/term-comp/Integer_Transition_Systems/From_AProVE_2014/*.smt2 benchmarks/term-comp/Integer_Transition_Systems/From_T2/*.smt2 | LC_ALL=C sort
