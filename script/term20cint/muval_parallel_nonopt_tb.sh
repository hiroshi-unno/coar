SCRIPT_DIR=$(
    cd $(dirname $0)/..
    pwd
)
timeout=1200 options='-c ./config/solver/muval_nonopt_parallel_tb.json -p ltsterm ' $SCRIPT_DIR/run_bench_for_multicore.sh benchmarks/LTS/term-comp/C_Integer/Stroeder_15_t2/*.t2 benchmarks/LTS/term-comp/C_Integer/Ton_Chanh_15_t2/*.t2 | LC_ALL=C sort
