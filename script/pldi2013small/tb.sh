SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-p cctl' $SCRIPT_DIR/para_tbp_tbd_muval_bench.sh benchmarks/C/pldi2013ctl/small/*.c | LC_ALL=C sort
