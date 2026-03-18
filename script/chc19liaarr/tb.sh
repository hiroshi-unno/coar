SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/pcsat_tb.json -p pcsp' para=3 $SCRIPT_DIR/run_bench.sh benchmarks/chc-comp19/lia-lin-arr/*.smt2 | LC_ALL=C sort
