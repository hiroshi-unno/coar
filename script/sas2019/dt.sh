SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/muval_parallel_dt.json -p muclp' $SCRIPT_DIR/run_bench.sh benchmarks/muCLP/sas2019/*.hes | LC_ALL=C sort
