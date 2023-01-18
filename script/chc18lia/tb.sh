SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/pcsat_tb.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/chc-comp18/lia/*.smt2 | LC_ALL=C sort