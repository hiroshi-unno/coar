SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=10 options='-c ./config/solver/z3_smt.json -p smt' $SCRIPT_DIR/run_bench.sh benchmarks/SMT/QF_LIRA/*/*.smt2 | LC_ALL=C sort