SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=600 options='../other_solvers/eldarica/eld' type=sygus $SCRIPT_DIR/run_any_solver_with_smt2.sh benchmarks/sygus-comp/comp/2019/Inv_Track/Lustre/*.sl | LC_ALL=C sort
