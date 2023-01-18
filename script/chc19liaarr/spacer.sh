SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/spacer.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/chc-comp19/lia-lin-arr/*.smt2 | LC_ALL=C sort
