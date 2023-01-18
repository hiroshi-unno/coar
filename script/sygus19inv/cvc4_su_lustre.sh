SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=600 options='../other_solvers/cvc4  --sygus-unif-boolean-heuristic-dt --sygus-active-gen=var-agnostic --sygus-add-const-grammar --decision=justification' type=sygus $SCRIPT_DIR/run_any_solver.sh benchmarks/sygus-comp/comp/2019/Inv_Track/Lustre/*.sl | LC_ALL=C sort
