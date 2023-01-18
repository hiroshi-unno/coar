SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=10 options='-c ./config/solver/z3_smt.json -p smt' $SCRIPT_DIR/run_bench.sh benchmarks/QSMT/LRA/*/*.smt2 benchmarks/QSMT/LRA/*/*/*.smt2 | LC_ALL=C sort