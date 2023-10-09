#!/bin/bash

cd $(dirname $0)/..

# Table 1. Spacer
timeout=600 options="-c ./config/solver/rcaml_wopp_spacer.json -p ml" para=4 \
    ./script/run_bench_para.sh ./benchmarks/OCaml/popl24/arm/*.ml \
    | LC_ALL=C sort \
    1> ./popl24ae/results_spacer.csv

# Table 1. PCSat
timeout=600 options="-c ./config/solver/rcaml_pcsat_tb_ar.json -p ml" para=4 \
    ./script/run_bench_para.sh ./benchmarks/OCaml/popl24/arm/*.ml \
    | LC_ALL=C sort \
    1> ./popl24ae/results_pcsat.csv

# Table 2.
timeout=600 options="-c ./config/solver/rcaml_wopp_spacer.json -p ml" para=4 \
    ./script/run_bench_para.sh ./benchmarks/OCaml/popl24/cps/*.ml \
    | LC_ALL=C sort \
    1> ./popl24ae/results_cps.csv