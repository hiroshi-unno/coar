SCRIPT_DIR=$(
    cd $(dirname $0)/..
    pwd
)
timeout=600 options='-p muclp' $SCRIPT_DIR/para_tbp_tbd_ar_nu_muval_bench.sh benchmarks/muCLP/popl2023mod/*.hes benchmarks/muCLP/popl2023mod/*/*/*.hes | LC_ALL=C sort
