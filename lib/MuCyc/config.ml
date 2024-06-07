open Core
open Common.Util

type cex_typ = QE | Model | MBP of int
(* 0 : use latest, 1 : use saved, 2 : use saved loop invariant *)
[@@deriving yojson]

type com_typ =
  | Or
  | Return of bool (* cex accumulation *)
  | Yield of
      bool (* query weakening *) * bool (* share trace among coroutines *)
[@@deriving yojson]

type strategy = Solve | Refine of cex_typ * com_typ [@@deriving yojson]

type cshare =
  | Level
  | Global of bool (* use saved *)
[@@deriving yojson]

type induct =
  | Normal of bool (* use disjuncts *)
  | Light of bool (* use disjuncts *)
[@@deriving yojson]

type t = {
  verbose : bool;
  simplify : bool;
  reduce : bool;
  slice_forward : bool;
  slice_backward : bool;
  gen_lemmas_with_ai : bool;
  gen_determ_conjs : bool;
  pcsp_solver : PCSPSolver.Config.t ext_file;
  refinement_strategy : strategy;
  timeout_check_valid : int;
  timeout_prove_each_conj : int;
      (* options for software model checking [PLDI'24] *)
  top_down_search : bool;
      (* true: top-down proof search a la PPDP'09
         false: bottom-up proof search a la Spacer *)
  monotone_trace : bool;
  induction : induct option;
  query_reuse : bool;
  counterexample_sharing : cshare option;
  backup_for_interp : bool;
  backup_for_mbp : bool;
  enable_pvar_elim : bool;
  check_validity : bool;
  (* options for relational verification [CAV'17] *)
  ask_pred_app_to_unfold : bool;
  valid_with_smt_threshold : int option;
  induct_threshold : int option;
  enable_apply_threshold : bool;
  normalize_lemma : bool;
  check_lemma_lhs : bool;
  fold_lemmas : bool;
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  Or_error.(
    PCSPSolver.Config.load_ext_file cfg.pcsp_solver >>= fun pcsp_solver ->
    Ok { cfg with pcsp_solver })

let load_ext_file = function
  | ExtFile.Instance x -> Ok (ExtFile.Instance x)
  | Filename filename -> (
      let open Or_error in
      try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
      match of_yojson raw_json with
      | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
      | Error msg ->
          error_string
          @@ sprintf "Invalid MuCyc Configuration (%s): %s" filename msg)
