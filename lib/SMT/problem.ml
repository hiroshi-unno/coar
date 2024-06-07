open Ast.LogicOld

type envs = {
  uni_senv : sort_env_map;
  exi_senv : sort_env_map;
  kind_map : Ast.Kind.map;
  fenv : FunEnv.t;
  dtenv : DTEnv.t;
}

type t = Formula.t
type solution = Sat of model | Unsat | Unknown

type incsol =
  | IncSat of model * (t -> incsol)
  | IncUnsat of (t -> incsol)
  | IncUnknown of (t -> incsol)

let str_of_solution = function
  | Sat model -> "sat\nmodel: " ^ str_of_model model
  | Unsat -> "unsat"
  | Unknown -> "unknown"
