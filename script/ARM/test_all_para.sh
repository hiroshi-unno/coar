SCRIPT_DIR=$(
    cd $(dirname $0)/..
    pwd
)
config_file="config/solver/rcaml_pcsat_tb_ar.json"
# config_file="config/solver/rcaml_no_fail_pcsat_tb_ar.json"
# config_file="config/solver/rcaml_no_part_pcsat_tb_ar.json"

# config_file="config/solver/rcaml_adt_inv_pcsat_tb_ar.json"
# config_file="config/solver/rcaml_adt_inv_no_fail_pcsat_tb_ar.json"
# config_file="config/solver/rcaml_adt_inv_no_part_pcsat_tb_ar.json"

# config_file="config/solver/rcaml_wo_pp_pcsat_tb_ar.json"
# config_file="config/solver/rcaml_wo_pp_no_fail_pcsat_tb_ar.json"
# config_file="config/solver/rcaml_wo_pp_no_part_pcsat_tb_ar.json"

# config_file="config/solver/rcaml_elem_pred_no_fail_pcsat_tb_ar.json"
# config_file="config/solver/rcaml_elem_pred_no_part_pcsat_tb_ar.json"
# config_file="config/solver/rcaml_elem_pred_pcsat_tb_ar.json"

timeout=600 options="-c $config_file -p ml" para=10 $SCRIPT_DIR/run_bench_para.sh benchmarks/OCaml/safety/alg_eff/ARM_bench/eff/*.ml | LC_ALL=C sort
