SCRIPT_DIR=$(
    cd $(dirname $0)/..
    pwd
)
timeout=600 options='-c ./config/solver/muval_prove_tb_ar.json -p muclp' $SCRIPT_DIR/run_bench.sh benchmarks/muCLP/popl2023mod/*.hes benchmarks/muCLP/popl2023mod/*/*/*.hes | LC_ALL=C sort
