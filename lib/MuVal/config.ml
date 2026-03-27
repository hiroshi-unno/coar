open Core
open Common.Util

type mode =
  | Auto
  | Prove
  | Disprove
  | Parallel
  | ParallelExc  (** with exchange of learned clauses *)
[@@deriving yojson]

type sm_kind =
  | SSM (* Streett supermartingale (SSM) *)
  | GSSM (* generalized Streett supermartingale (GSSM) *)
  | LexGSSM (* lexicographic GSSM (LexGSSM) *)
  | PMSM (* progress-measure supermartingale (PMSM) *)
  | LexPMSM (* lexicographic PMSM (LexPMSM) *)
[@@deriving yojson]

type t = {
  verbose : bool;
  output_iteration : bool;
  output_yes_no : bool;
  output_time : bool;
  output_witness : bool;
  check_problem : bool;
  (* validity checking for muCLP *)
  optimizer : MuCLP.Optimizer.Config.t ext_file;
  mode : mode;
  number_of_pairs : int;
  use_parity_progress_measure : bool;
  use_scc : bool;
  use_alternation_depth : bool;
  ignore_nu_components : bool;
  qelim : MuCLP.Qelim.Config.t;
  gen_extra_partial_sols : bool;
  random_ex_size : int;
  random_ex_bound : int;
  send_lower_bounds : bool;
  pcsp_solver_primal : PCSPSolver.Config.t ext_file;
  pcsp_solver_dual : PCSPSolver.Config.t ext_file;
  (* validity checking for Quantitative Fixpoint Logic *)
  quant_prefp_templ_num_conds : int;
  quant_prefp_templ_use_orig_ite : bool;
  quant_prefp_templ_cond_degree : int;
  quant_prefp_templ_term_degree : int;
  quant_rank_templ_num_conds : int;
  quant_rank_templ_use_orig_ite : bool;
  quant_rank_templ_cond_degree : int;
  quant_rank_templ_term_degree : int;
  quant_postfp_templ_num_conds : int;
  quant_postfp_templ_use_orig_ite : bool;
  quant_postfp_templ_cond_degree : int;
  quant_postfp_templ_term_degree : int;
  quant_postfp_force_non_const : bool;
  quant_underapprox_templ_cond_degree : int option;
  quant_underapprox_templ_term_degree : int option;
  quant_omega_regular_inv_shape : int list;
  quant_omega_regular_supermartingale : sm_kind;
  enable_pareto_caching : int option;
  pareto_cache_timeout : int option;
  pareto_cache_num_conds : int;
  pareto_cache_cond_degree : int;
  pareto_cache_zero_reward : bool;
  dist_bound_use_l1_norm : bool;
  dist_bound_use_optimathsat : bool;
  dist_bound_initialize_standard_basis : bool;
  dist_bound_use_strict_bound : bool;
  dist_bound_relax : float option;
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  Or_error.(
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver_primal
    >>= fun pcsp_solver_primal ->
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver_dual
    >>= fun pcsp_solver_dual ->
    MuCLP.Optimizer.Config.load_ext_file cfg.optimizer >>= fun optimizer ->
    MuCLP.Qelim.Config.instantiate_ext_files cfg.qelim >>= fun qelim ->
    Ok { cfg with pcsp_solver_primal; pcsp_solver_dual; optimizer; qelim })

let load_ext_file = function
  | ExtFile.Instance x -> Ok (ExtFile.Instance x)
  | Filename filename -> (
      let open Or_error in
      try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
      match of_yojson raw_json with
      | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
      | Error msg ->
          error_string
          @@ sprintf "Invalid MuVal Configuration (%s): %s" filename msg)
