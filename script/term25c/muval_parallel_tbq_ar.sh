SCRIPT_DIR=$(
    cd $(dirname $0)/..
    pwd
)
timeout=300 options='-c ./config/solver/muval_parallel_tbq_ar.json -p ltsterm ' para=2 $SCRIPT_DIR/run_bench.sh benchmarks/LTS/term-comp/C/AProVE_memory_alloca/*.t2 benchmarks/LTS/term-comp/C/AProVE_memory_unsafe/*.t2 benchmarks/LTS/term-comp/C/AProVE_numeric/*.t2 benchmarks/LTS/term-comp/C/Hensel_22/*.t2 benchmarks/LTS/term-comp/C/Stroeder_15/*.t2 benchmarks/LTS/term-comp/C/SV-COMP_Mixed_Categories/*.t2 benchmarks/LTS/term-comp/C/SV-COMP_Termination_Category/*.t2 benchmarks/LTS/term-comp/C/Ton_Chanh_15/*.t2 benchmarks/LTS/term-comp/C/Ultimate/*.t2 | LC_ALL=C sort
