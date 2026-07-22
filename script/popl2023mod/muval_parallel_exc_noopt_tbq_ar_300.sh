SCRIPT_DIR=$(
    cd $(dirname $0)/..
    pwd
)
timeout=300 options='-c ./config/solver/muval_parallel_exc_noopt_tbq_ar.json -p muclp' para=2 $SCRIPT_DIR/run_bench.sh benchmarks/muCLP/popl2023mod/*.hes benchmarks/muCLP/popl2023mod/*/*/*.hes | LC_ALL=C sort
