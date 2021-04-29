#!/bin/bash

source ./script/muval_dt_term_comp_20rc

for file in "${benchmarks[@]}"; do
    timeout=$timeout prove_config=./config/solver/muval_dt_prove_lazy_term_comp_thr.json disprove_config=./config/solver/muval_dt_disprove_lazy_term_comp_thr.json options='-p ltsterm' ./script/para_muval_prove_disprove.sh benchmarks/term-comp20/$file 2>/dev/null
done
