SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/pcsat_dt.json -p pcsp' para=3 $SCRIPT_DIR/run_bench.sh benchmarks/pfwnCSP/function/*.clp | LC_ALL=C sort
