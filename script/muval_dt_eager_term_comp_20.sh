#!/bin/bash

source ./script/muval_dt_term_comp_20rc

for file in "${benchmarks[@]}"; do
    timeout=$timeout prove_config=./config/solver/muval_dt_prove_eager_term_comp_nu.json disprove_config=./config/solver/muval_dt_disprove_eager_term_comp_nu.json options='-p ltsterm' ./script/para_muval_prove_disprove.sh benchmarks/term-comp20/$file 2>/dev/null
done
