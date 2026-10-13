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
  verbose : bool; [@default false]
  output_iteration : bool; [@default true]
  output_yes_no : bool; [@default false]
  output_time : bool; [@default false]
  output_witness : bool; [@default false]
  check_problem : bool; [@default false]
  (* validity checking for muCLP *)
  optimizer : MuCLP.Optimizer.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/muval/optimizer/enable.json"]
  mode : mode; [@default Prove]
  number_of_pairs : int; [@default 1]
  use_parity_progress_measure : bool; [@default false]
  use_scc : bool; [@default true]
  use_alternation_depth : bool; [@default true]
  pack_rank_components : bool; [@default false]
      (** in the parity-progress-measure reduction with alternation depth, pack
          the ranking components in pairs, so that a family compares
          ceil((amax+1)/2) components and a priority [p] is compared at
          component ceil(p/2) (Kura and Unno, "Solving First-Order Fixed-Point
          Logics via a Least-to-Greatest Transformation Based on Game
          Semantics", Def. 7.8).  Expressiveness is unchanged; acceptance is
          still decided by the parity of [p]. *)
  qelim : MuCLP.Qelim.Config.t; [@default Common.Util.config_default MuCLP.Qelim.Config.of_yojson "{}"]
  output_certificates : string option; [@default None]
  gen_extra_partial_sols : bool; [@default false]
  random_ex_size : int; [@default 0]
  random_ex_bound : int; [@default 0]
  send_lower_bounds : bool; [@default false]
  pcsp_solver_primal : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat_tb_ar_fixpoint.json"]
  pcsp_solver_dual : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat_tb_ar_fixpoint.json"]
  (* validity checking for Quantitative Fixpoint Logic *)
  quant_prefp_templ_num_conds : int; [@default 1]
  quant_prefp_templ_use_orig_ite : bool; [@default false]
  quant_prefp_templ_cond_degree : int; [@default 1]
  quant_prefp_templ_term_degree : int; [@default 1]
  enable_geometric_pla : bool; [@default false]
  quant_rank_templ_num_conds : int; [@default 1]
  quant_rank_templ_use_orig_ite : bool; [@default false]
  quant_rank_templ_cond_degree : int; [@default 1]
  quant_rank_templ_term_degree : int; [@default 1]
  quant_postfp_templ_num_conds : int; [@default 1]
  quant_postfp_templ_use_orig_ite : bool; [@default false]
  quant_postfp_templ_cond_degree : int; [@default 1]
  quant_postfp_templ_term_degree : int; [@default 1]
  quant_postfp_force_non_const : bool; [@default false]
  quant_underapprox_templ_cond_degree : int option; [@default Some 1]
  quant_underapprox_templ_term_degree : int option; [@default None]
  quant_omega_regular_inv_shape : int list; [@default [ 1 ]]
  quant_omega_regular_supermartingale : sm_kind; [@default LexPMSM]
  enable_pareto_caching : int option; [@default None]
  pareto_cache_timeout : int option; [@default None]
  pareto_cache_num_conds : int; [@default 4]
  pareto_cache_cond_degree : int; [@default 1]
  pareto_cache_zero_reward : bool; [@default false]
  dist_bound_use_l1_norm : bool; [@default false]
  dist_bound_use_optimathsat : bool; [@default false]
  dist_bound_initialize_standard_basis : bool; [@default false]
  dist_bound_use_strict_bound : bool; [@default false]
  dist_bound_relax : float option; [@default Some 0.1]
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

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "MuVal"
  let instantiate = instantiate_ext_files
end)
