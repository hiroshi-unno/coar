SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=300 options='-c ./config/solver/pcsat_tb_polyhedron_domain_2_null.json -p sygus' $SCRIPT_DIR/run_bench.sh benchmarks/sygus-comp/comp/2018/Inv_Track/*.sl | LC_ALL=C sort
