SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=600 options='-c ./config/solver/hoice.json -p sygus' $SCRIPT_DIR/run_bench.sh benchmarks/sygus-comp/comp/2019/Inv_Track/*/*.sl | LC_ALL=C sort
