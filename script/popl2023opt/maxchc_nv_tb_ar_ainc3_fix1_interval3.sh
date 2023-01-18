SCRIPT_DIR=$(
    cd $(dirname $0)/..
    pwd
)
timeout=600 options='-c ./config/solver/optpcsat_nv_tb_ar_ainc3_fix1_interval3.json -p chcmax' $SCRIPT_DIR/run_bench_for_maxopt.sh benchmarks/CHC/popl2023opt/*.smt2 | LC_ALL=C sort
