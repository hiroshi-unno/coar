open Core
open Common
open Common.Util
open Ast
open PCSatCommon

module Config = struct
  type strategy =
    | Template of TBSynthesizer.Config.t  (** configuration for TBSynthesizer *)
    | Classification of CBSynthesizer.Config.t
        (** configuration for CBSynthesizer [DT/GSC/SCQM/LTB] *)
    | PredicateAbstraction of PASynthesizer.Config.t
        (** configuration for PASynthesizer [PASAT/PASID] *)
  [@@deriving yojson]

  type t = {
    verbose : bool;
    strategy : strategy;
    check_candidates : bool;
        (** check whether candidates satisfy the examples *)
    refine_candidates : bool;
        (** refine candidates until they satisfy the examples *)
  }
  [@@deriving yojson]

  let instantiate_ext_files cfg =
    let open Or_error in
    match cfg.strategy with
    | Template strategy_cfg ->
        TBSynthesizer.Config.instantiate_ext_files strategy_cfg
        >>= fun strategy_cfg -> Ok { cfg with strategy = Template strategy_cfg }
    | Classification strategy_cfg ->
        CBSynthesizer.Config.instantiate_ext_files strategy_cfg
        >>= fun strategy_cfg ->
        Ok { cfg with strategy = Classification strategy_cfg }
    | PredicateAbstraction strategy_cfg ->
        PASynthesizer.Config.instantiate_ext_files strategy_cfg
        >>= fun strategy_cfg ->
        Ok { cfg with strategy = PredicateAbstraction strategy_cfg }

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid Synthesizer Configuration (%s): %s" filename msg
        )

  module type ConfigType = sig
    val config : t
  end
end

module type SynthesizerType = sig
  val run_phase : int -> State.u -> State.s Or_error.t
  val init : unit -> unit
end

module Make
    (RLCfg : RLConfig.ConfigType)
    (Cfg : Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) : SynthesizerType = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module CandidateChecker =
    CandidateChecker.Make
      ((val Debug.Config.(if config.verbose then enable else disable)))
      (APCSP)

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  module Synthesizer =
    (val match config.strategy with
         | Config.Template cfg ->
             (module TBSynthesizer.Make
                       (RLCfg)
                       (struct
                         let config = cfg
                       end)
                       (APCSP) : SynthesizerType)
         | Classification cfg ->
             (module CBSynthesizer.Make
                       (struct
                         let config = cfg
                       end)
                       (APCSP) : SynthesizerType)
         | PredicateAbstraction cfg ->
             (module PASynthesizer.Make
                       (struct
                         let config = cfg
                       end)
                       (APCSP) : SynthesizerType))

  let init () = Synthesizer.init ()

  let check_candidates ?(inst = true) ~id fenv exi_senv (sample : ExClauseSet.t)
      (cands : CandSol.t list) =
    let constrs =
      Set.Poly.map sample ~f:(fun cl ->
          let senv, phi = ExClause.to_old_formula cl in
          (cl, Logic.of_old_sort_env_map senv, Logic.ExtTerm.of_old_formula phi))
    in
    List.find_map cands ~f:(fun cand ->
        let sub = CandSol.to_subst cand in
        let psenv = Map.Poly.key_set @@ fst cand in
        let cex =
          Set.find constrs ~f:(fun (_, uni_senv, phi) ->
              let phi =
                Logic.ExtTerm.to_old_fml exi_senv uni_senv
                  (Logic.Term.subst sub phi)
              in
              let phi =
                LogicOld.Formula.forall (LogicOld.get_dummy_term_senv ())
                @@
                let bounds =
                  Map.to_alist @@ Logic.to_old_sort_env_map uni_senv
                in
                (if inst then
                   LogicOld.Formula.subst
                     (Map.Poly.of_alist_exn
                     @@ List.map bounds ~f:(fun (x, s) ->
                            (x, LogicOld.Term.mk_dummy s)))
                 else LogicOld.Formula.forall bounds)
                @@ phi
              in
              assert (Set.is_subset (LogicOld.Formula.fvs_of phi) ~of_:psenv);
              not
              @@ Evaluator.is_valid (Z3Smt.Z3interface.is_valid ~id fenv) phi)
        in
        match cex with
        | None -> None
        | Some (clause, _, _) -> Some (cand, clause))

  let check_candidates e =
    if config.check_candidates && not config.refine_candidates then (
      let open State.Monad_infix in
      Debug.print
      @@ lazy "** checking whether the candidates satisfy the examples";
      Ok e >>=? fun vs cands ->
      match
        check_candidates ~id ~inst:true vs.fenv
          (PCSP.Problem.senv_of APCSP.problem)
          (VersionSpace.examples_of vs)
          (List.map ~f:fst cands)
      with
      | None -> Ok e
      | Some (cand, clause) ->
          Debug.print @@ lazy "The candidate\n";
          Debug.print @@ lazy (Ast.CandSol.str_of cand);
          Debug.print @@ lazy "\nviolates the following example\n";
          Debug.print @@ lazy (ExClause.str_of clause);
          Debug.print @@ lazy "\nThis may be a bug of the synthesizer.";
          (* Or_error.error_string "Error in Synthesizer.check_candidates" *)
          Ok e)
    else Ok e

  let run_phase iters e =
    if RLCfg.config.enable then (
      if RLCfg.config.show_examples then (
        RLConfig.lock ();
        let examples = State.pos_neg_und_examples_of e in
        Debug.print_stdout
        @@ lazy
             (sprintf "examples: %s" @@ Yojson.Safe.to_string
             @@ VersionSpace.to_yojson examples);
        RLConfig.unlock ());
      if RLCfg.config.show_elapsed_time then (
        RLConfig.lock ();
        Debug.print_stdout @@ lazy "begin synthesizer";
        RLConfig.unlock ());
      let tm = Timer.make () in
      let res = Or_error.(Synthesizer.run_phase iters e >>= check_candidates) in
      if RLCfg.config.show_elapsed_time then (
        RLConfig.lock ();
        Debug.print_stdout @@ lazy (sprintf "end synthesizer: %f" (tm ()));
        RLConfig.unlock ());
      res)
    else Or_error.(Synthesizer.run_phase iters e >>= check_candidates)

  let rec refine_cands iters e =
    let open Or_error.Monad_infix in
    run_phase iters e >>= function
    | State.Continue (vs, cands) -> (
        match CandidateChecker.check_candidates vs (List.map ~f:fst cands) with
        | `Unsat -> Ok State.Unsat
        | `Valid ->
            Debug.print @@ lazy " The new candidate is valid.";
            Ok (State.Continue (vs, cands))
        | `Invalid (pos, neg, und) ->
            Debug.print
            @@ lazy " The new candidate is invalid, restart synthesizer.";
            refine_cands iters @@ State.of_examples vs
            @@ Set.Poly.map ~f:(fun (ex, srcs) ->
                   ( ex,
                     List.map srcs ~f:(fun c ->
                         (ClauseGraph.mk_example c, true)) ))
            @@ Set.Poly.union_list [ pos; neg; und ])
    | _ -> assert false

  let run_phase = if config.refine_candidates then refine_cands else run_phase
end

let make rl_config config problem =
  (module Make
            (struct
              let config = rl_config
            end)
            (struct
              let config = config
            end)
            (struct
              let problem = problem
            end) : SynthesizerType)
