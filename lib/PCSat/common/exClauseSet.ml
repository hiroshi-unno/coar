open Core
open Common.Combinator
open Common.Ext
open Ast
open Ast.LogicOld

type t = ExClause.t Set.Poly.t

(* Assuming that all pure formulas are evaluated into T/F. *)
let of_formula exi_senv phi : t =
  Set.Poly.filter_map ~f:(uncurry3 @@ ExClause.make exi_senv)
  @@ Formula.cnf_of exi_senv phi

let of_model exi_senv pex (senv, phi) (* clause*) model : t =
  let map =
    senv |> Map.Poly.to_alist
    |> List.map ~f:(fun (id, sort) ->
           ( (id, sort),
             match List.find model ~f:(fun ((x, _), _) -> Stdlib.(id = x)) with
             | None -> None
             | Some (_, v) -> v ))
    |> List.map ~f:(function
         | (x, _), Some v ->
             (*print_endline (Ident.name_of_tvar x ^ " |-> " ^ Term.str_of v)*)
             (x, v)
         | (x, s), None ->
             (*print_endline (Ident.name_of_tvar x ^ " |-> *");*)
             let sort = Logic.ExtTerm.to_old_sort s in
             if pex then
               ( x,
                 Term.mk_var
                   (Ident.mk_fresh_dontcare (Ident.name_of_tvar x))
                   sort )
             else (x, Term.mk_dummy sort))
    |> Map.Poly.of_alist_exn
  in
  (*print_endline @@ sprintf "[of_model] before:%s\n" (Formula.str_of phi);*)
  Formula.subst map phi
  |> Normalizer.normalize_let ~rename:true
  |> Formula.nnf_of |> Formula.instantiate_div0_mod0 |> Evaluator.simplify
  |> Normalizer.normalize
  (*|> Formula.elim_let
    |> Evaluator.simplify
    |> Normalizer.normalize*)
  (*|> (fun phi -> print_endline @@ sprintf "[of_model] after :%s" (Formula.str_of phi); phi)*)
  |> Formula.cnf_of (Logic.to_old_sort_env_map exi_senv)
  |> Set.Poly.filter_map ~f:(uncurry3 @@ ExClause.make exi_senv)
  |> Set.Poly.map ~f:(ExClause.normalize_params (Map.key_set exi_senv))

let exatoms_of = Set.concat_map ~f:ExClause.exatoms_of
let exatoms_of_uclauses = Set.Poly.map ~f:ExClause.exatom_of_uclause

let classify_examples examples =
  let pos, examples' = Set.partition_tf examples ~f:ExClause.is_unit_positive in
  let neg, und = Set.partition_tf examples' ~f:ExClause.is_unit_negative in
  (pos, neg, und)

let to_clause_set exi_senv sample =
  ClauseSet.of_formulas exi_senv @@ Set.Poly.map ~f:ExClause.to_formula sample

let str_of ?(max_display = Some 20) sample =
  (match max_display with
  | None -> Set.to_list sample
  | Some max_display -> List.take (Set.to_list sample) max_display)
  |> String.concat_map_list ~sep:";\n" ~f:ExClause.str_of
  |> fun res ->
  res
  ^
  match max_display with
  | None -> ""
  | Some max_display -> if Set.length sample > max_display then ";.." else ""

let normalize = Set.Poly.map ~f:ExClause.normalize
let instantiate = Set.Poly.map ~f:ExClause.instantiate
let refresh_params senv = Set.Poly.map ~f:(ExClause.refresh_params senv)

let refresh_params_with_src senv =
  Set.Poly.map ~f:(fun (ex, src) -> (ExClause.refresh_params senv ex, src))

let inter_check ?(enable = true) pos_atoms neg_atoms =
  if not enable then Set.inter pos_atoms neg_atoms |> Set.Poly.map ~f:fst
  else
    let atm_eq atm1 atm2 =
      match (ExAtom.to_old_atom atm1, ExAtom.to_old_atom atm2) with
      | ( Some (_, (Atom.App (psym1, _, _) as atm1)),
          Some (_, (Atom.App (psym2, _, _) as atm2)) ) -> (
          if Stdlib.(psym1 <> psym2) then false
          else
            try Option.is_some @@ Atom.unify Set.Poly.empty atm1 atm2
            with _ -> false)
      | _ -> false
    in
    Set.fold pos_atoms ~init:Set.Poly.empty ~f:(fun confits (atm1, _) ->
        Set.fold neg_atoms ~init:confits ~f:(fun confits (atm2, _) ->
            if atm_eq atm1 atm2 then
              Set.union confits @@ Set.Poly.of_list [ atm1; atm2 ]
            else confits))

let unit_propagation unknowns
    (pos_clauses : (ExClause.t * ExClause.t list) Set.Poly.t)
    (neg_clauses : (ExClause.t * ExClause.t list) Set.Poly.t)
    (undecided : (ExClause.t * ExClause.t list) Set.Poly.t) =
  let rec inner pos neg und =
    let pos_atms =
      Set.Poly.map pos ~f:(fun (ex, srcs) ->
          (ExClause.exatom_of_uclause ex, srcs))
    in
    let neg_atms =
      Set.Poly.map neg ~f:(fun (ex, srcs) ->
          (ExClause.exatom_of_uclause ex, srcs))
    in
    let conflicts = inter_check pos_atms neg_atms in
    if Fn.non Set.is_empty conflicts then `Unsat conflicts
    else
      let und =
        Set.Poly.filter_map
          ~f:(ExClause.simplify unknowns pos_atms neg_atms)
          und
      in
      if Set.exists und ~f:(fun (ex, _) -> ex |> ExClause.is_empty) then
        `Unsat Set.Poly.empty (* ToDo: recover conflicting literals *)
      else
        let ucs, nucs =
          Set.partition_tf und ~f:(fun (ex, _) -> ExClause.is_unit ex)
        in
        if Set.is_empty ucs then `Result (pos, neg, und)
        else
          let pos', neg' =
            Set.partition_tf ucs ~f:(fst >> ExClause.is_unit_positive)
          in
          inner (Set.union pos pos') (Set.union neg neg') nucs
  in
  let pos =
    Set.Poly.map pos_clauses ~f:(fun (ex, srcs) ->
        (ExClause.normalize ex, srcs))
  in
  let neg =
    Set.Poly.map neg_clauses ~f:(fun (ex, srcs) ->
        (ExClause.normalize ex, srcs))
  in
  let und =
    Set.Poly.map undecided ~f:(fun (ex, srcs) -> (ExClause.normalize ex, srcs))
  in
  inner pos neg und

let check_candidates ?(inst = true) ~id fenv exi_senv (sample : t)
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
              Logic.ExtTerm.to_old_fml exi_senv
                (uni_senv, Logic.Term.subst sub phi)
            in
            let phi =
              LogicOld.Formula.forall (LogicOld.get_dummy_term_senv ())
              @@
              let bounds = Map.to_alist @@ Logic.to_old_sort_env_map uni_senv in
              (if inst then
                 LogicOld.Formula.subst
                   (Map.Poly.of_alist_exn
                   @@ List.map bounds ~f:(fun (x, s) ->
                          (x, LogicOld.Term.mk_dummy s)))
               else LogicOld.Formula.forall bounds)
              @@ phi
            in
            assert (Set.is_subset (LogicOld.Formula.fvs_of phi) ~of_:psenv);
            not @@ Evaluator.is_valid (Z3Smt.Z3interface.is_valid ~id fenv) phi)
      in
      match cex with None -> None | Some (clause, _, _) -> Some (cand, clause))

let discard_unused_exs pcsp exs =
  let senv = PCSP.Problem.senv_of pcsp in
  Set.filter exs ~f:(fun ex ->
      let pvar_sorts = ExClause.pvar_sorts_of ex in
      not
      @@ Set.exists pvar_sorts ~f:(fun (Ident.Pvar v, sorts) ->
             let tvar = Ident.Tvar v in
             if PCSP.Problem.is_ord_pred pcsp tvar then
               match Map.Poly.find senv tvar with
               | None -> true
               | Some sort ->
                   let sorts' =
                     Logic.Sort.args_of sort
                     |> List.map ~f:Logic.ExtTerm.to_old_sort
                   in
                   Stdlib.(sorts' <> sorts)
             else true))
