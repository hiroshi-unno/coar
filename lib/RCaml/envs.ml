open Core

let cgen_config = ref {
    Ast.Rtype.depend_on_func_args = false;
    Ast.Rtype.depend_on_unit_args = false;
    Ast.Rtype.instantiate_svars_to_int = false;
    Ast.Rtype.gen_ref_pred_for_fun_types = false;
    Ast.Rtype.gen_type_temp_for_constrs = false;
    Ast.Rtype.never_fail = false;
    Ast.Rtype.can_fail_only_at_total_apps = false;
    Ast.Rtype.can_cause_temp_eff_only_at_total_apps = false;
    Ast.Rtype.enable_temp_eff = false
  }
let denv = ref (Ast.LogicOld.DTEnv.mk_empty ())
let renv = ref (Ast.Rtype.Env.mk_empty ())
