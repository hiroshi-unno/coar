SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/hoice.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/chc-comp20/test/LIA-lin/*.smt2 | LC_ALL=C sort
