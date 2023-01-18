open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

type t = Predicate.fixpoint * Ident.pvar * sort_env_list * Formula.t

let make fix pvar args formula : t = (fix, pvar, args, formula)

let map f (fp, pvar, params, phi) = fp, pvar, params, f phi
let map_list f = List.map ~f:(map f)

let let_ pred = pred
let fixpoint_of = function (fix, _, _, _) -> fix
let pvar_of = function (_, pvar, _, _) -> pvar
let args_of = function (_, _, args, _) -> args
let body_of = function (_, _, _, body) -> body
let pvars_of_list = List.map ~f:pvar_of
let pred_sort_env_of_list preds =
  Set.Poly.of_list @@ List.map preds ~f:(fun (_, pvar, params, _) -> pvar, List.map ~f:snd params)
let pred_sort_env_map_of_list map preds =
  let rec inner map = function
    | [] -> map
    | (_, pvar, params, _) :: preds ->
      let sorts = List.map ~f:snd params in
      let map' = Map.Poly.add_exn map ~key:pvar ~data:sorts in
      inner map' preds
  in
  inner map preds

let sort_env_of_list preds =
  Set.Poly.of_list @@ List.map preds ~f:(fun (_, pvar, params, _) -> Ident.pvar_to_tvar pvar, Logic.ExtTerm.of_old_sort @@ Sort.mk_fun @@ List.map ~f:snd params @ [T_bool.SBool])
let subst tsub (fix, pvar, args, body) =
  let tsub = Map.remove_keys tsub (List.map ~f:fst args) in
  (fix, pvar, args, Formula.subst tsub body)

let str_of (fix, Ident.Pvar pvar_name, args, body) =
  Printf.sprintf "%s%s: bool =%s %s;"
    pvar_name
    (if List.length args > 0 then " " ^ str_of_sort_env_list Term.str_of_sort args else "")
    (Predicate.str_of_fixpoint fix)
    (Formula.str_of body)
let str_of_ (fix, Ident.Pvar pvar_name, args, body) =
  Printf.sprintf "%s(%s) =%s %s"
    pvar_name
    (String.concat_map_list ~sep:"," ~f:(fst >> Ident.name_of_tvar) args)
    (Predicate.str_of_fixpoint fix)
    (Formula.str_of body)
let str_of_list preds = String.concat_map_list ~sep:"\n" ~f:str_of preds
let pr_list ppf preds = Format.fprintf ppf "%s" (str_of_list preds)

let rec replace_app (replacer: Formula.t -> Formula.t) formula =
  if Formula.is_atom formula then
    let atom, info = Formula.let_atom formula in
    let formula = Formula.mk_atom atom ~info in
    if Atom.is_app atom then
      let pred, _, _ = Atom.let_app atom in
      if Predicate.is_var pred then replacer formula else formula
    else formula
  else if Formula.is_binop formula then
    let binop, left, right, info = Formula.let_binop formula in
    Formula.mk_binop binop (replace_app replacer left) (replace_app replacer right) ~info
  else if Formula.is_unop formula then
    let unop, body, info = Formula.let_unop formula in
    Formula.mk_unop unop (replace_app replacer body) ~info
  else if Formula.is_bind formula then
    let binder, bounds, body, info = Formula.let_bind formula in
    Formula.mk_bind binder bounds (replace_app replacer body) ~info
  else assert false
let get_next_list fml =
  let res = ref [] in
  let _ = replace_app (fun fml ->
      let atom, _ = Formula.let_atom fml in
      let pred, _, _ = Atom.let_app atom in
      let pvar, _ = Predicate.let_var pred in
      res := pvar :: !res;
      fml)
      fml
  in
  Stdlib.List.sort_uniq Ident.pvar_compare !res
let replace_app_add formula arg sort =
  replace_app (fun fml ->
      let atom, info = Formula.let_atom fml in
      let pred, args, info' = Atom.let_app atom in
      let pvar, arg_sorts = Predicate.let_var pred in
      Formula.mk_atom ~info
        (Atom.mk_app ~info:info'
           (Predicate.mk_var pvar (sort :: arg_sorts))
           (arg :: args)))
    formula
let elim_mu_with_rec preds tvar_rec =
  List.map preds ~f:(fun (fix, pvar, args, body) ->
      let args = (tvar_rec, T_int.SInt) :: args in
      let term = Term.mk_var tvar_rec T_int.SInt in
      if Stdlib.(fix = Predicate.Nu) then
        let body = replace_app_add body term T_int.SInt in
        make Predicate.Nu pvar args body
      else
        (* replace all F X Y --> F (rec_ - 1) X Y in body*)
        let term = Term.mk_fsym_app T_int.Sub [term; T_int.one ()] in
        let body = replace_app_add body term T_int.SInt in
        (* body --> rec_ > 0 /\ body *)
        let body = Formula.mk_and (Formula.mk_atom (T_int.mk_gt term (T_int.zero ()))) body in
        make Predicate.Nu pvar args body)
