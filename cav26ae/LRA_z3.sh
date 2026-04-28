cd `dirname $0`; cd ..
timeout=300 options='-c ./config/solver/z3_smt.json -p smt' para=1 ./cav26ae/run_bench.sh benchmarks/QSMT/LRA/*/*.smt2 benchmarks/QSMT/LRA/*/*/*.smt2 | LC_ALL=C sort