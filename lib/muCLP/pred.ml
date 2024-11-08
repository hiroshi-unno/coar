open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

type t = Predicate.fixpoint * Ident.pvar * sort_env_list * Formula.t

let make fix pvar args formula : t = (fix, pvar, args, formula)
let map f (fp, pvar, params, phi) = (fp, pvar, params, f phi)
let map_list f = List.map ~f:(map f)
let let_ pred = pred
let fixpoint_of = function fix, _, _, _ -> fix
let pvar_of = function _, pvar, _, _ -> pvar
let args_of = function _, _, args, _ -> args
let body_of = function _, _, _, body -> body
let pvars_of_list = List.map ~f:pvar_of

let pred_sort_env_of_list preds =
  Set.Poly.of_list
  @@ List.map preds ~f:(fun (_, pvar, params, _) ->
         (pvar, List.map ~f:snd params))

let pred_sort_env_map_of_list map preds =
  let rec inner map = function
    | [] -> map
    | (_, pvar, params, _) :: preds ->
        let sorts = List.map ~f:snd params in
        let map' = Map.Poly.add_exn map ~key:pvar ~data:sorts in
        inner map' preds
  in
  inner map preds

let to_formula (fix, pvar, args, body) =
  let atm = Formula.mk_atom @@ Atom.pvar_app_of_senv pvar args in
  match fix with
  | Predicate.Mu -> Formula.mk_imply body atm
  | Predicate.Nu -> Formula.mk_imply atm body
  | Predicate.Fix -> failwith "to_formula"

let sort_env_of_list preds =
  Set.Poly.of_list
  @@ Logic.of_old_sort_env_list 
  @@ List.map preds ~f:(fun (_, pvar, params, _) ->
         Term.pred_to_sort_bind (pvar, List.map ~f:snd params))

let subst tsub (fix, pvar, args, body) =
  let tsub = Map.remove_keys tsub (List.map ~f:fst args) in
  (fix, pvar, args, Formula.subst tsub body)

let lookup preds pvar =
  match List.find preds ~f:(fun (_, pvar', _, _) -> Stdlib.(pvar = pvar')) with
  | Some (fix, _, args, body) -> Some (fix, args, body)
  | None -> None

let str_of (fix, Ident.Pvar pvar_name, args, body) =
  sprintf "%s%s: bool =%s %s;" pvar_name
    (if List.length args > 0 then
       " " ^ str_of_sort_env_list Term.str_of_sort args
     else "")
    (Predicate.str_of_fop fix) (Formula.str_of body)

let str_of_ (fix, Ident.Pvar pvar_name, args, body) =
  sprintf "%s(%s) =%s %s" pvar_name
    (String.concat_map_list ~sep:"," ~f:(fst >> Ident.name_of_tvar) args)
    (Predicate.str_of_fop fix) (Formula.str_of body)

let str_of_list preds = String.concat_map_list ~sep:"\n" ~f:str_of preds
let pr_list ppf preds = Format.fprintf ppf "%s" (str_of_list preds)

let replace_app_add formula arg sort =
  Formula.map_atom formula ~f:(function
    | Atom.App (Predicate.Var (pvar, arg_sorts), args, info) ->
        Formula.mk_atom
        @@ Atom.mk_pvar_app ~info pvar (sort :: arg_sorts) (arg :: args)
    | atm -> Formula.mk_atom atm)

let elim_mu_with_rec preds tvar_rec =
  List.map preds ~f:(fun (fix, pvar, args, body) ->
      let args = (tvar_rec, T_int.SInt) :: args in
      let term = Term.mk_var tvar_rec T_int.SInt in
      if Stdlib.(fix = Predicate.Nu) then
        let body = replace_app_add body term T_int.SInt in
        make Predicate.Nu pvar args body
      else
        (* replace all F X Y --> F (rec_ - 1) X Y in body*)
        let term = Term.mk_fsym_app T_int.Sub [ term; T_int.one () ] in
        let body = replace_app_add body term T_int.SInt in
        (* body --> rec_ > 0 /\ body *)
        let body =
          Formula.mk_and
            (Formula.mk_atom (T_int.mk_gt term (T_int.zero ())))
            body
        in
        make Predicate.Nu pvar args body)
