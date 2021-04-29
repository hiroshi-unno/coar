open Core
open Common.Util
open Ast
open Ast.LogicOld

type t = ExClause.t Set.Poly.t

(* Assuming that all pure formulas are evaluated into T/F. *)
let of_formula exi_senv phi : t =
  Set.Poly.filter_map ~f:(uncurry3 @@ ExClause.make exi_senv) @@
  Formula.cnf_of (Logic.SortMap.key_set exi_senv) phi

let of_model exi_senv pex (senv, phi)(* clause*) model : t =
  let map =
    senv
    |> Logic.SortMap.to_alist
    |> List.map ~f:(fun (id, sort) ->
        (id, sort),
        match List.find model ~f:(fun ((x, _), _) -> Stdlib.(=) id x) with
        | None -> None | Some (_, v) -> v)
    |> List.map ~f:(function
        | (x, _), Some v ->
          (*print_endline (Ident.name_of_tvar x ^ " |-> " ^ Term.str_of v)*)
          x, v
        | (x, s), None ->
          (*print_endline (Ident.name_of_tvar x ^ " |-> *");*)
          let sort = Logic.ExtTerm.to_old_sort s in
          if pex then x, Term.mk_var (Ident.mk_fresh_dontcare (Ident.name_of_tvar x)) sort
          else x, Term.mk_dummy sort)
    |> Map.Poly.of_alist_exn
  in
  Formula.subst map phi
  |> Formula.nnf_of
  |> Formula.instantiate_div0_mod0
  |> Evaluator.simplify
  |> Normalizer.normalize
  |> Formula.cnf_of (Logic.SortMap.key_set exi_senv)
  |> Set.Poly.filter_map ~f:(uncurry3 @@ ExClause.make exi_senv)
  |> Set.Poly.map ~f:ExClause.normalize_params

let exatoms_of = Set.concat_map ~f:ExClause.exatoms_of
let exatoms_of_uclauses = Set.Poly.map ~f:ExClause.exatom_of_uclause

let to_clause_set exi_senv sample =
  ClauseSet.of_formulas exi_senv @@ Set.Poly.map ~f:ExClause.to_formula sample

let str_of ?(max_display=Some 20) sample =
  (match max_display with None -> Set.Poly.to_list sample | Some max_display -> List.take (Set.Poly.to_list sample) max_display)
  |> List.map ~f:ExClause.str_of
  |> String.concat ~sep:";\n"
  |> (fun res -> res ^ (match max_display with None -> "" | Some max_display -> if Set.Poly.length sample > max_display then ";.." else ""))

let normalize = Set.Poly.map ~f:ExClause.normalize
let instantiate = Set.Poly.map ~f:ExClause.instantiate

let refresh_params senv = Set.Poly.map ~f:(ExClause.refresh_params senv)

let inter_check ?(enable=true) pos_atoms neg_atoms =
  if not @@ enable then Set.Poly.inter pos_atoms neg_atoms
  else
    let atm_eq atm1 atm2 =
      match (ExAtom.to_old_atom atm1, ExAtom.to_old_atom atm2) with
      | Some (_, (Atom.App(psym1, _, _) as atm1)), Some (_, (Atom.App(psym2, _, _) as atm2)) -> 
        if Stdlib.(<>) psym1 psym2 then false
        else Option.is_some @@ Atom.unify Set.Poly.empty atm1 atm2 
      | _ -> false
    in
    Set.Poly.fold pos_atoms ~init:(Set.Poly.empty) ~f:(
      fun confits atm1 -> 
        Set.Poly.fold neg_atoms ~init:confits ~f:(
          fun confits atm2 ->
            if atm_eq atm1 atm2 then Set.Poly.union confits @@ Set.Poly.of_list [atm1; atm2]
            else confits
        ))

let unit_propagation npfvs (pos_clauses: t) (neg_clauses: t) (undecided: t) =
  let rec inner pos neg und =
    let pos_atms = Set.Poly.map pos ~f:ExClause.exatom_of_uclause in
    let neg_atms = Set.Poly.map neg ~f:ExClause.exatom_of_uclause in
    let conflicts = inter_check pos_atms neg_atms in
    if not @@ Set.Poly.is_empty conflicts then
      `Unsat conflicts
    else
      let und = Set.Poly.filter_map ~f:(ExClause.simplify npfvs pos_atms neg_atms) und in
      if Set.Poly.exists und ~f:ExClause.is_empty then
        `Unsat Set.Poly.empty(* ToDo: recover conflicting literals *)
      else
        let ucs, nucs = Set.Poly.partition_tf und ~f:ExClause.is_unit in
        if Set.Poly.is_empty ucs then
          `Result (pos, neg, und)
        else
          let pos', neg' = Set.Poly.partition_tf ucs ~f:ExClause.is_unit_positive in
          inner (Set.Poly.union pos pos') (Set.Poly.union neg neg') nucs
  in
  inner (normalize pos_clauses) (normalize neg_clauses) (normalize undecided)

let check_candidates ?(inst=true) exi_senv (sample: t) (cands : CandSol.t list) =
  let constrs = Set.Poly.map sample ~f:(fun cl ->
      let senv, phi = ExClause.to_old_formula cl in
      cl,
      Logic.SortMap.of_old_sort_map Logic.ExtTerm.of_old_sort senv,
      Logic.ExtTerm.of_old_formula phi)
  in
  let fenv = Set.Poly.empty in (*TODO: generate fenv*)
  List.find_map cands ~f:(fun cand ->
      let sub = CandSol.to_subst cand in
      let psenv = Set.Poly.of_list @@ Map.Poly.keys @@ fst cand in
      let cex =
        Set.Poly.find constrs ~f:(fun (_, uni_senv, phi) ->
            let phi = Logic.ExtTerm.to_old_formula (Logic.SortMap.merge exi_senv uni_senv) (Logic.Term.subst sub phi) [] in
            let phi =
              LogicOld.Formula.forall !LogicOld.dummy_term_senv @@
              let bounds = Logic.SortMap.to_old_sort_env Logic.ExtTerm.to_old_sort uni_senv in
              (if inst then
                 LogicOld.Formula.subst
                   (Map.Poly.of_alist_exn @@ 
                    LogicOld.SortEnv.map bounds ~f:(fun (x, s) -> x, LogicOld.Term.mk_dummy s))
               else
                 LogicOld.Formula.forall bounds)
                phi
            in
            assert (Set.Poly.is_subset (LogicOld.Formula.fvs_of phi) ~of_:psenv);
            not @@ Evaluator.is_valid (Z3Smt.Z3interface.is_valid fenv) phi) in
      match cex with
      | None -> None
      | Some (clause, _, _) -> Some (cand, clause))
