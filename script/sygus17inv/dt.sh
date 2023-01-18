SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/pcsat_dt.json -p sygus' $SCRIPT_DIR/run_bench.sh benchmarks/sygus-comp/comp/2017/Inv_Track/*.sl | LC_ALL=C sort
