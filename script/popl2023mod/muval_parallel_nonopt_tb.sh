SCRIPT_DIR=$(
    cd $(dirname $0)/..
    pwd
)
timeout=600 options='-c ./config/solver/muval_parallel_nonopt_tb.json -p muclp' $SCRIPT_DIR/run_bench_for_multicore.sh benchmarks/muCLP/popl2023mod/*.hes benchmarks/muCLP/popl2023mod/*/*/*.hes | LC_ALL=C sort
