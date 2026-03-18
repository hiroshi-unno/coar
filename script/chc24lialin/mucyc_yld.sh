SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=600 options='-c ./config/solver/mucyc_yieldTT_mbp1_indNF.json -p pcsp' para=3 $SCRIPT_DIR/run_bench.sh benchmarks/chc-comp24/LIA-Lin/*.smt2 | LC_ALL=C sort
