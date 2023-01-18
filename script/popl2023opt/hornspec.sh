SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=600 options='./hornspec' type=maxchc $SCRIPT_DIR/run_any_solver_with_log.sh benchmarks/CHC/popl2023opt/*.smt2 | LC_ALL=C sort
