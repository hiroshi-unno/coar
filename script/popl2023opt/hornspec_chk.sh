SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=600 options='_build/default/main.exe -c ./config/solver/optpcsat_chk_sol.json -p chcmax' $SCRIPT_DIR/run_any_solver_with_log.sh benchmarks/CHC/popl2023opt/*.smt2 | LC_ALL=C sort
