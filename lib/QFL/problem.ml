open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld

(* ToDo *)
module Debug = Debug.Make ((val Debug.Config.disable))

type kind = LB | UB

type check = {
  params : sort_env_list;
  left : Formula.t option;
  kind : kind;
  name : Ident.tvar;
  args : Term.t list;
  bound : Term.t;
  strict : bool;
}

type dist_check = {
  name : Ident.tvar;
  args : Term.t list;
  params : sort_env_list;
  bound : Formula.t;
}

type query =
  | ASAT of (Ident.tvar * Term.t list) option * sort_env_list * Formula.t
  (* almost sure satisfaction of omega regular properties *)
  | Check (* bounds checking *) of check
  | DistCheck (* distribution bounds checking *) of dist_check

type t = { preds : Pred.t list; query : query }
type solution = Valid | Invalid | Unknown | Timeout

let make preds query = { preds; query }
let flip_solution = function Valid -> Invalid | Invalid -> Valid | x -> x

let formula_of_query = function
  | ASAT _ -> failwith "ASAT not implemented"
  | Check query ->
      let right =
        (if query.strict then
           match query.kind with LB -> Formula.lt | UB -> Formula.gt
         else match query.kind with LB -> Formula.leq | UB -> Formula.geq)
          query.bound
          (Term.mk_fvar_app query.name
             (List.map query.args ~f:(Fn.const T_real.SReal))
             T_real.SReal query.args)
      in
      let body =
        match query.left with
        | None -> right
        | Some left -> Formula.mk_imply left right
      in
      if List.is_empty query.params then body
      else Formula.forall query.params body
  | DistCheck _ -> failwith "DistCheck not implemented"

let str_of_solution = function
  | Valid -> "valid"
  | Invalid -> "invalid"
  | Unknown -> "unknown"
  | Timeout -> "timeout"

let str_of_query ?(fsub = None) = function
  | ASAT (None, param_senv, param_constr) ->
      sprintf "ASAT (%s) | %s"
        (str_of_sort_env_list Term.str_of_sort param_senv)
        (Formula.str_of param_constr)
  | ASAT (Some (var, args), param_senv, param_constr) ->
      sprintf "ASAT (%s %s) (%s) | %s" (Ident.name_of_tvar var)
        (String.concat_map_list ~sep:" " ~f:Term.str_of args)
        (str_of_sort_env_list Term.str_of_sort param_senv)
        (Formula.str_of param_constr)
  | Check query -> (
      let q = formula_of_query (Check query) in
      Formula.str_of
      @@ match fsub with None -> q | Some fsub -> Formula.subst_funcs fsub q)
  | DistCheck query ->
      let dist =
        Term.mk_fvar_app query.name
          (List.map query.args ~f:(fun t -> Term.sort_of t))
          T_real.SReal query.args
      in
      sprintf "dist (%s) ensures %s -> (%s)" (Term.str_of dist)
        (str_of_sort_env_list Term.str_of_sort query.params)
        (Formula.str_of query.bound)

let str_of ?(fsub = None) qfl =
  sprintf "%s\ns.t.\n%s"
    (str_of_query ~fsub qfl.query)
    (Pred.str_of_list qfl.preds)

let has_only_mu qfl =
  List.for_all ~f:(fun pred -> Stdlib.( = ) pred.kind Predicate.Mu) qfl.preds

let has_only_nu qfl =
  List.for_all ~f:(fun pred -> Stdlib.( = ) pred.kind Predicate.Nu) qfl.preds

let size_of qfl = List.length qfl.preds

let depth_of qfl =
  List.fold ~init:1 qfl.preds ~f:(fun lv pred ->
      match pred.kind with
      | Predicate.Mu -> if lv % 2 = 1 then lv else lv + 1
      | Predicate.Nu -> if lv % 2 = 0 then lv else lv + 1
      | Predicate.Fix -> failwith "depth_of")

let level_of qfl tvar =
  let lv, found =
    List.fold ~init:(1, false) qfl.preds ~f:(fun (lv, found) pred ->
        if found then (lv, found)
        else
          let lv' =
            match pred.kind with
            | Predicate.Mu -> if lv % 2 = 1 then lv else lv + 1
            | Predicate.Nu -> if lv % 2 = 0 then lv else lv + 1
            | Predicate.Fix -> failwith "level_of"
          in
          if Ident.tvar_equal tvar pred.name then (lv', true) else (lv', false))
  in
  if found then lv else failwith "level_of: not found"

let simplify_query = function
  | ASAT (init, param_senv, param_constr) ->
      ASAT (init, param_senv, Evaluator.simplify param_constr)
  | Check query ->
      Check { query with bound = Evaluator.simplify_term query.bound }
  | DistCheck query ->
      DistCheck
        {
          name = query.name;
          args = List.map query.args ~f:Evaluator.simplify_term;
          params = query.params;
          bound = Evaluator.simplify query.bound;
        }

let simplify qfl =
  {
    preds = List.map ~f:Pred.simplify qfl.preds;
    query = simplify_query qfl.query;
  }

let fvars_of pred =
  Set.Poly.filter_map (Term.fvar_apps_of pred.Pred.body) ~f:(function
    | Term.FunApp (LogicOld.FVar (f, _, _), _, _) -> Some f
    | _ -> None)

let unfold qfl =
  let fvars = Set.Poly.of_list @@ Pred.pvars_of_list qfl.preds in
  let fs =
    Set.inter fvars @@ Set.Poly.union_list
    @@ List.map qfl.preds ~f:(fun pred -> Pred.fvs_of pred)
  in
  let preds, funs =
    List.partition_map qfl.preds ~f:(fun pred ->
        if
          (not (Set.mem fs pred.name))
          || (Set.is_empty @@ Set.inter fvars @@ Pred.fvs_of pred)
        then Second (pred.name, (pred.args, pred.body))
        else First pred)
  in
  let fsub = Map.Poly.of_alist_exn funs in
  ( fsub,
    {
      preds = List.map preds ~f:(Pred.subst_funcs fsub);
      query = qfl.query (* fsub is not applied to the query *);
    } )

let nth i qfl =
  try
    let found = ref false in
    let f t =
      if T_tuple.is_tuple_cons t then (
        let _, elems, _ = T_tuple.let_tuple_cons t in
        found := true;
        List.nth_exn elems i)
      else t
    in
    let res =
      {
        preds =
          List.map qfl.preds ~f:(fun pred ->
              { pred with body = Term.map_term true ~f pred.body });
        query =
          (match qfl.query with
          | ASAT (init, param_senv, param_constr) ->
              ASAT (init, param_senv, Formula.map_term ~f param_constr)
          | Check query ->
              Check { query with bound = Term.map_term true ~f query.bound }
          | DistCheck query -> DistCheck query (*ToDo*));
      }
    in
    if !found then Some res else None
  with _ -> None

let unroll qfl n =
  let get_unroll_func_and_base qfl =
    match qfl.query with
    | ASAT _ -> failwith "lower_bounds_by_unroll: ASAT not supported"
    | Check query -> (
        match
          Map.Poly.find
            (Map.Poly.of_alist_exn
            @@ List.map qfl.preds ~f:(fun pred -> (pred.name, pred)))
            query.name
        with
        | None -> failwith "lower_bounds_by_unroll: predicate not found"
        | Some _ ->
            let query_fun_app =
              Term.mk_fvar_app query.name
                (List.map ~f:snd query.params)
                T_real.SReal (* May be changed? *) query.args
            in
            let subst_pred =
              Map.Poly.of_alist_exn
                (List.map ~f:(fun p -> (p.name, (p.args, p.body))) qfl.preds)
            in
            ( (fun x ->
                Evaluator.simplify_term @@ Normalizer.normalize_term
                @@ Term.subst_funcs subst_pred x),
              query_fun_app ))
    | _ -> failwith "lower_bounds_by_unroll: not supported"
  in
  let subst_zero =
    Map.Poly.of_alist_exn
      (List.map ~f:(fun p -> (p.name, (p.args, T_real.rzero ()))) qfl.preds)
  in
  let fsub, query_fun_app = get_unroll_func_and_base qfl in
  let k = ref query_fun_app in
  for _ = 1 to n do
    k := fsub !k
  done;
  Evaluator.simplify_term @@ Normalizer.normalize_term
  @@ Term.subst_funcs subst_zero !k

let replace_bound_with qfl bound' =
  {
    qfl with
    query =
      (match qfl.query with
      | ASAT _ -> failwith "not implemented for ASAT"
      | Check query -> Check { query with bound = bound' }
      | _ -> failwith "not implemented");
  }
