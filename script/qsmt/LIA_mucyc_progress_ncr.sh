SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/mucyc_progress_nc.json -p smt' para=3 $SCRIPT_DIR/run_bench.sh benchmarks/QSMT/LIA/*/*.smt2 | LC_ALL=C sort