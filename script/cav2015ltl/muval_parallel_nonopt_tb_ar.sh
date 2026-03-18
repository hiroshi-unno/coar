SCRIPT_DIR=$(
    cd $(dirname $0)/..
    pwd
)
timeout=600 options='-c ./config/solver/muval_parallel_nonopt_tb_ar.json -p cltl' para=1 $SCRIPT_DIR/../run_bench.sh benchmarks/C/cav2015ltl/*/*.c benchmarks/C/cav2015ltl/*/*/*.c | LC_ALL=C sort
