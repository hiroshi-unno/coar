SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/pcsat_tb.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/chc-comp20/test/LIA/*.smt2 | LC_ALL=C sort
