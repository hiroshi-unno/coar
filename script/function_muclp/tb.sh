SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-p muclp' $SCRIPT_DIR/para_tbp_tbd_muval_bench.sh benchmarks/muCLP/function/*.hes | LC_ALL=C sort
