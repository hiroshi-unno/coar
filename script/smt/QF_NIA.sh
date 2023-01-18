SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=10 options='-c ./config/solver/z3_smt.json -p smt' $SCRIPT_DIR/run_bench.sh benchmarks/SMT/QF_NIA/20170427-VeryMax/CInteger/*.smt2 | LC_ALL=C sort
timeout=10 options='-c ./config/solver/z3_smt.json -p smt' $SCRIPT_DIR/run_bench.sh benchmarks/SMT/QF_NIA/20170427-VeryMax/ITS/*.smt2 | LC_ALL=C sort
timeout=10 options='-c ./config/solver/z3_smt.json -p smt' $SCRIPT_DIR/run_bench.sh benchmarks/SMT/QF_NIA/*/*.smt2 benchmarks/SMT/QF_NIA/20170427-VeryMax/SAT14/*.smt2 | LC_ALL=C sort