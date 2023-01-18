SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/muval_parallel_dt.json -p cctl' $SCRIPT_DIR/run_bench.sh benchmarks/C/pldi2013ctl/industrial/*.c | LC_ALL=C sort
