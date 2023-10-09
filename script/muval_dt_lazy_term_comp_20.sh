#!/bin/bash

source ./script/muval_dt_term_comp_20rc

for file in "${benchmarks[@]}"; do
    timeout=$timeout prove_config=./config/solver/muval_term_comp_prove_nu_dt_lazy.json disprove_config=./config/solver/muval_term_comp_disprove_nu_dt_lazy.json options='-p ltsterm' ./script/para_muval_prove_disprove.sh benchmarks/term-comp20/$file 2> /dev/null
done
