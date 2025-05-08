open Core
open Common
open Common.Ext
open Common.Combinator
open PCSatCommon
open Ast
open Ast.LogicOld

module Make
    (Verbose : Debug.Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) =
struct
  module Debug = Debug.Make (Verbose)

  let fenv = PCSP.Problem.fenv_of APCSP.problem
  let id = PCSP.Problem.id_of APCSP.problem
  let _ = Debug.set_id id

  let check_clause =
    let check_history = Hashtbl.Poly.create () in
    fun ?(smt_timeout = None) phi ->
      match Hashtbl.Poly.find check_history phi with
      | Some model -> model
      | None ->
          let model =
            Z3Smt.Z3interface.check_sat ~timeout:smt_timeout fenv
              [ Formula.mk_neg phi ]
          in
          Hashtbl.add_exn check_history ~key:phi ~data:model;
          model

  let of_cand_and_ex ?(smt_timeout = None) uenv exi_senv (cl : ExClause.t)
      ((params_senv, cand) : CandSol.t) =
    let clause, uni_senv =
      let senv, phi = ExClause.to_old_formula cl in
      (Logic.ExtTerm.of_old_formula phi, Logic.of_old_sort_env_map senv)
    in
    let sub = CandSol.to_subst (params_senv, cand) in
    let phi =
      Logic.ExtTerm.to_old_fml exi_senv uni_senv (Logic.Term.subst sub clause)
    in
    let phi = UTermEnv.subst_formula uenv @@ Evaluator.simplify phi in
    match check_clause ~id ~smt_timeout phi with
    | `Sat model ->
        (* not all but some clause in cls caused a countermodel *)
        Debug.print @@ lazy (sprintf "[of_cand_and_ex] %s" (ExClause.str_of cl));
        Debug.print
        @@ lazy
             ("phi: "
             ^ (Formula.str_of @@ Formula.mk_neg phi)
             ^ "\nmodel: " ^ str_of_model model);
        UTermEnv.update_by_model uenv model;
        let cond =
          Formula.and_of
          @@ List.filter_map model ~f:(function
               | (tvar, _), Some term -> (
                   try
                     let term1, _ = UTermEnv.of_tvar uenv tvar in
                     Some (Formula.eq term1 term)
                   with _ -> None)
               | _ -> None)
        in
        let sub =
          List.fold model ~init:Map.Poly.empty ~f:(fun ret -> function
            | (tvar, _), Some term -> Map.Poly.add_exn ret ~key:tvar ~data:term
            | _ -> ret)
        in
        let unknowns = Map.key_set exi_senv in
        let res =
          Set.Poly.singleton
            (ExClause.subst sub cl |> ExClause.add_cond cond
            |> ExClause.normalize_params unknowns)
        in
        if Fn.non Set.is_empty res then
          (* note that res never represents true *)
          Set.Poly.map res ~f:(fun ex -> (ex, [ cl ]))
        else
          let ctx = Z3.mk_context [ ("MODEL", "true") ] in
          let dtenv =
            Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx
              (PCSP.Problem.dtenv_of APCSP.problem)
          in
          failwith
            (sprintf "model: %s\ncandidate: %s\nphi: %s\nz3 input: %s"
               (str_of_model model)
               (CandSol.str_of (params_senv, cand))
               (Formula.str_of phi)
               (Z3.Expr.to_string
               @@ Z3Smt.Z3interface.of_formula ~id ctx [] [] fenv dtenv
               @@ Formula.mk_neg phi))
    | `Unsat -> Set.Poly.empty
    | _ ->
        (*failwith "Z3 reported unknown or timeout in the validation phase"*)
        Set.Poly.singleton (ExClause.mk_unit_pos @@ ExAtom.mk_true (), [])
  (*dummy*)

  let of_cand_and_exs ?(smt_timeout = None) vs cls (cand : CandSol.t) =
    let uenv = vs.VersionSpace.uenv in
    Set.fold cls ~init:Set.Poly.empty ~f:(fun exs cl ->
        if
          not
          @@ ExClause.exists cl
               ~f:
                 (ExAtom.exists ~f:(fun term ->
                      Term.is_var term || T_dt.is_sdt (Term.sort_of term)))
        then exs
        else
          let exs' =
            of_cand_and_ex ~smt_timeout uenv
              (PCSP.Problem.senv_of APCSP.problem)
              cl cand
          in
          Set.union exs exs')

  let str_of_conflicts conflicts =
    "********* conflicts *********\n"
    ^ String.concat_map_set ~sep:", " ~f:ExAtom.str_of conflicts

  let check_candidate ?(smt_timeout = None) vs (cand : CandSol.t) =
    let dpos, dneg, und = VersionSpace.pos_neg_und_examples_of vs in
    let dpos' = of_cand_and_exs ~smt_timeout vs dpos cand in
    let dneg' = of_cand_and_exs ~smt_timeout vs dneg cand in
    let und' = of_cand_and_exs ~smt_timeout vs und cand in
    if not (Set.is_empty dpos' && Set.is_empty dneg' && Set.is_empty und') then (
      let exs = Set.union dpos' dneg' |> Set.union und' in
      Debug.print
      @@ lazy
           (sprintf "The candidate: \n%s\n is invalid/" (CandSol.str_of cand));
      Debug.print
      @@ lazy
           ("Uninterpreted terms env after candidate checking:"
          ^ UTermEnv.str_of vs.uenv);
      Debug.print
      @@ lazy
           "*** Counterexamples of parametric-examples to the Candidate \
            Solutions:";
      Debug.print
      @@ lazy (String.concat_map_set ~sep:";\n" exs ~f:(fst >> ExClause.str_of));
      Debug.print @@ lazy "*************************************");
    (dpos', dneg', und')

  let check_candidates ?(smt_timeout = None) vs (cands : CandSol.t list) =
    let dpos, dneg, und = VersionSpace.pos_neg_und_examples_of vs in
    let dpos', dneg', und' =
      List.fold cands ~init:(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
        ~f:(fun (dpos, dneg, und) cand ->
          let dpos', dneg', und' = check_candidate ~smt_timeout vs cand in
          (Set.union dpos dpos', Set.union dneg dneg', Set.union und und'))
    in
    if Set.is_empty dpos' && Set.is_empty dneg' && Set.is_empty und' then `Valid
    else
      let dpos = Set.Poly.map dpos ~f:(fun ex -> (ex, [ ex ])) in
      let dneg = Set.Poly.map dneg ~f:(fun ex -> (ex, [ ex ])) in
      let und = Set.Poly.map und ~f:(fun ex -> (ex, [ ex ])) in
      let dpos, dneg, und =
        (Set.union dpos dpos', Set.union dneg dneg', Set.union und und')
      in
      match
        ExClauseSet.unit_propagation
          (Map.key_set @@ PCSP.Problem.senv_of APCSP.problem)
          dpos dneg und
      with
      | `Unsat conflicts ->
          Debug.print @@ lazy (str_of_conflicts conflicts);
          `Unsat
      | `Result (dpos', dneg', und') -> `Invalid (dpos', dneg', und')
end
