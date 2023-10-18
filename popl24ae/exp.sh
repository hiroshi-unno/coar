#!/bin/bash

timeout=600 # time limit in seconds
para=4 # the number of parallel executions
memlimit=256 # memory limit in GB

cd $(dirname $0)/..

# Table 1. Spacer
outfile="./popl24ae/results_spacer.csv"
memusage="./popl24ae/memusage_spacer.csv"
benchmarks=$(awk -F, -v memlimit="$memlimit" '$2 <= memlimit*1024*1024 { print $1 }' $memusage)
timeout=$timeout options="-c ./config/solver/rcaml_wopp_spacer.json -p ml" para=$para \
    ./script/run_bench_para.sh $benchmarks \
    1> $outfile
# add the lines of the excluded benchmarks
awk -F, -v memlimit="$memlimit" '$2 > memlimit*1024*1024 { OFS=","; print $1,"(excluded)" }' $memusage >> $outfile

# Table 1. PCSat
outfile="./popl24ae/results_pcsat.csv"
memusage="./popl24ae/memusage_pcsat.csv"
benchmarks=$(awk -F, -v memlimit="$memlimit" '$2 <= memlimit*1024*1024 { print $1 }' $memusage)
timeout=$timeout options="-c ./config/solver/rcaml_pcsat_tb_ar.json -p ml" para=$para \
    ./script/run_bench_para.sh $benchmarks \
    1> $outfile
# add the lines of the excluded benchmarks
awk -F, -v memlimit="$memlimit" '$2 > memlimit*1024*1024 { OFS=","; print $1,"(excluded)" }' $memusage >> $outfile


# # Table 2.
outfile="./popl24ae/results_cps.csv"
memusage="./popl24ae/memusage_cps.csv"
benchmarks=$(awk -F, -v memlimit="$memlimit" '$2 <= memlimit*1024*1024 { print $1 }' $memusage)
timeout=$timeout options="-c ./config/solver/rcaml_wopp_spacer.json -p ml" para=$para \
    ./script/run_bench_para.sh $benchmarks \
    1> $outfile
# add the lines of the excluded benchmarks
awk -F, -v memlimit="$memlimit" '$2 > memlimit*1024*1024 { OFS=","; print $1,"(excluded)" }' $memusage >> $outfile
