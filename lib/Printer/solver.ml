open Core
open Common.Util
open Preprocessing

module type SolverType = sig
  val print_sat : SAT.Problem.t -> unit
  val print_dqsat : DQSAT.Problem.t -> unit
  val print_hosat : HOSAT.Problem.t -> unit
  val print_homc : HOMC.Problem.t -> unit
  val print_smt : SMT.Problem.t -> unit

  (*val string_of_pcsp : PCSP.Problem.t -> string*)
  val print_pcsp : PCSP.Problem.t -> unit Or_error.t
  val print_muclp : MuCLP.Problem.t -> unit
  val print_lts : LTS.Problem.t -> unit
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  let preprocessor =
    let open Or_error in
    ExtFile.unwrap config.preprocessor >>= fun cfg -> Ok (Preprocessor.make cfg)

  (*let string_of_pcsp pcsp =
    match config.smt_format with
    | SMT2 ->
        Smtlib2.of_pcsp ~id:None (*ToDo*)
          ~add_missing_forall:config.add_missing_forall pcsp
    | String -> PCSP.Problem.str_of pcsp*)

  let print_homc = HOMC.Problem.pr Format.std_formatter

  let print_sat cnf =
    match config.sat_format with
    | HOMC ->
        let module HOMCSat = HOMCSat.Solver.Make (struct
          let config = config.homc_sat
        end) in
        print_homc @@ HOMCSat.homc_of_hosat @@ HOSAT.Problem.of_sat cnf
    | String -> print_endline @@ SAT.Problem.str_of cnf

  let print_dqsat dqsat =
    match config.sat_format with
    | HOMC ->
        let module HOMCSat = HOMCSat.Solver.Make (struct
          let config = config.homc_sat
        end) in
        print_homc @@ HOMCSat.homc_of_hosat @@ HOSAT.Problem.of_dqsat dqsat
    | String -> print_endline @@ DQSAT.Problem.str_of dqsat

  let print_hosat hosat =
    match config.sat_format with
    | HOMC ->
        let module HOMCSat = HOMCSat.Solver.Make (struct
          let config = config.homc_sat
        end) in
        print_homc @@ HOMCSat.homc_of_hosat hosat
    | String -> print_endline @@ HOSAT.Problem.str_of hosat

  let print_pcsp pcsp =
    let open Or_error in
    preprocessor >>= fun (module Preprocessor) ->
    let defining_context =
      Poly.(config.smt_format = SMT2)
      && Smtlib2.has_supported_defining_context (PCSP.Problem.fenv_of pcsp)
    in
    let pcsp =
      if defining_context
      then
        (* Assertion-only elimination can choose a predicate's interpretation
           without substituting it in known defining equations. Keep the full
           clauses as well as the definitions for this context-preserving
           export path; otherwise the exported file can be satisfiable where
           the input with its definitions is not. *)
        pcsp
      else snd @@ Preprocessor.preprocess ~bpvs:Set.Poly.empty pcsp
    in
    return @@ print_endline
    @@ (match config.smt_format with
      | SMT2 ->
          Smtlib2.of_pcsp ~id:None (*ToDo*)
            ~add_missing_forall:config.add_missing_forall
      | String -> PCSP.Problem.str_of)
    @@ pcsp

  let print_muclp muclp = print_endline @@ MuCLP.Problem.str_of muclp

  (* an SMT problem is a single formula, so there is nothing to lay out *)
  let print_smt phi = print_endline @@ Ast.LogicOld.Formula.str_of phi

  let print_lts lts =
    match config.lts_format with
    | PCSP ->
        (* no reduction of an LTS to a pCSP exists in this tree; the MuCLP
           format is the one an LTS can be printed in *)
        Common.Refusal.refuse
          "lts_format PCSP: an LTS cannot be printed as a pCSP, since that \
           reduction has no implementation; use lts_format MuCLP"
    | MuCLP ->
        print_endline @@ MuCLP.Problem.str_of
        @@ MuCLP.Util.of_lts ~print:(fun _ -> ()) lts
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
