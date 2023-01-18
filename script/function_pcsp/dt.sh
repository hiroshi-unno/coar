SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/pcsat_dt.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/pfwnCSP/function/*.clp | LC_ALL=C sort
