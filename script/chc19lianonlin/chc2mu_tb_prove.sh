SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=1 options='-c ./config/solver/muval_prove_tb.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/chc-comp19/lia-nonlin/*.smt2 | LC_ALL=C sort
