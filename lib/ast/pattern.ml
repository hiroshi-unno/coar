open Core
open Common.Ext
open Ident
open LogicOld

(** Patterns *)

type t =
  | PAny of Sort.t
  | PVar of sort_bind
  | PTuple of t list
  | PCons of Datatype.t * string * t list

let mk_pvar tvar sort = PVar (tvar, sort)
let mk_ptuple tvars = PTuple tvars
let mk_pcons dt cons_name tvars = PCons (dt, cons_name, tvars)
let mk_pany sort = PAny sort
let is_pvar = function PVar _ -> true | _ -> false
let is_ptuple = function PTuple _ -> true | _ -> false
let is_pcons = function PCons _ -> true | _ -> false

let rec str_of ?(with_sort = false) = function
  | PAny sort -> "_" ^ if with_sort then " : " ^ Term.str_of_sort sort else ""
  | PVar (tvar, sort) ->
      name_of_tvar tvar
      ^ if with_sort then " : " ^ Term.str_of_sort sort else ""
  | PTuple pats ->
      String.paren
      @@ String.concat_map_list ~sep:", " pats ~f:(str_of ~with_sort)
  | PCons (t, cons_name, pats) ->
      sprintf "%s%s"
        (if with_sort then String.paren (cons_name ^ " : " ^ Datatype.str_of t)
         else cons_name)
      @@
      if List.is_empty pats then ""
      else
        String.paren
          (String.concat_map_list ~sep:", " pats ~f:(str_of ~with_sort))

let rec tvars_of = function
  | PAny _ -> Set.Poly.empty
  | PVar (tvar, _) -> Set.Poly.singleton tvar
  | PTuple pats | PCons (_, _, pats) ->
      Set.Poly.union_list @@ List.map pats ~f:tvars_of

let rec sort_of = function
  | PAny sort -> sort
  | PVar (_, sort) -> sort
  | PTuple pats -> T_tuple.STuple (List.map ~f:sort_of pats)
  | PCons (dt, _, _) -> Datatype.sort_of dt

let rec term_of = function
  | PAny sort -> Term.mk_var (mk_fresh_dontcare "_") sort
  | PVar (v, sort) -> Term.mk_var v sort
  | PTuple ps ->
      T_tuple.mk_tuple_cons (List.map ps ~f:sort_of) @@ List.map ps ~f:term_of
  | PCons (dt, cons, ps) -> T_dt.mk_cons dt cons @@ List.map ps ~f:term_of

let rec of_term = function
  | Term.Var (v, sort, _) when is_dontcare v -> mk_pany sort
  | Term.Var (v, sort, _) -> mk_pvar v sort
  | Term.FunApp (T_tuple.TupleCons _, ts, _) ->
      mk_ptuple @@ List.map ts ~f:of_term
  | Term.FunApp (T_dt.DTCons (cons, _, dt), ts, _) ->
      mk_pcons dt cons @@ List.map ts ~f:of_term
  | t -> failwith @@ sprintf "[of_term] %s is not a pattern" @@ Term.str_of t

let rec senv_of pat sort =
  match (pat, sort) with
  | PAny _, _ -> Map.Poly.empty
  | PVar (x, _sort), _ -> Map.Poly.singleton x sort
  | PTuple pats, T_tuple.STuple sorts ->
      Map.force_merge_list @@ List.map2_exn pats sorts ~f:senv_of
  | PCons (dt, cons_name, pats), T_dt.SDT dt'
    when String.(Datatype.name_of dt = Datatype.name_of dt') ->
      let sorts = Datatype.sorts_of_cons_name dt' cons_name in
      Map.force_merge_list @@ List.map2_exn pats sorts ~f:senv_of
  | _ -> failwith "senv_of"

let rec match_with pat term =
  match pat with
  | PAny _ -> Map.Poly.empty
  | PVar (x, _sort) -> Map.Poly.singleton x term
  | PTuple pats ->
      Map.force_merge_list
      @@ List.mapi pats ~f:(fun i pi ->
             match_with pi
             @@ T_tuple.mk_tuple_sel (List.map ~f:sort_of pats) term i)
  | PCons (dt, cons_name, pats) ->
      (*ToDo*)
      Map.force_merge_list
      @@ List.mapi pats ~f:(fun i pi ->
             match_with pi @@ T_dt.mk_sel_by_cons dt cons_name i term)

let rec subst_sort maps = function
  | PAny sort -> PAny (Term.subst_sort maps sort)
  | PVar (tvar, sort) -> PVar (tvar, Term.subst_sort maps sort)
  | PTuple pats -> PTuple (List.map pats ~f:(subst_sort maps))
  | PCons (t, cons_name, pats) ->
      PCons
        (Datatype.subst maps t, cons_name, List.map pats ~f:(subst_sort maps))
