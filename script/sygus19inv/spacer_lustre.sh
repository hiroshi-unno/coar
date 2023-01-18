SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=600 options='-c ./config/solver/spacer.json -p sygus' $SCRIPT_DIR/run_bench.sh benchmarks/sygus-comp/comp/2019/Inv_Track/Lustre/*.sl | LC_ALL=C sort
