open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

type t = {
  kind : Predicate.fixpoint;
  name : Ident.tvar;
  args : sort_env_list;
  body : Term.t;
}

let make kind name args body = { kind; name; args; body }
let map f pred = { pred with body = f pred.body }
let map_list f = List.map ~f:(map f)
let pvars_of_list = List.map ~f:(fun pred -> pred.name)

let pred_sort_env_of_list preds =
  Set.Poly.of_list
  @@ List.map preds ~f:(fun pred -> (pred.name, List.map ~f:snd pred.args))

let pred_sort_env_map_of_list map preds =
  let rec inner map = function
    | [] -> map
    | pred :: preds ->
        let sorts = List.map pred.args ~f:snd in
        let map' = Map.Poly.add_exn map ~key:pred.name ~data:sorts in
        inner map' preds
  in
  inner map preds

let to_formula pred =
  let term = Term.fvar_app_of_senv pred.name pred.args T_real.SReal in
  match pred.kind with
  | Predicate.Mu -> Formula.leq pred.body term
  | Predicate.Nu -> Formula.leq term pred.body
  | Predicate.Fix -> failwith "to_formula"

let sort_env_of_list preds =
  Set.Poly.of_list @@ Logic.of_old_sort_env_list
  @@ List.map preds ~f:(fun pred ->
         (pred.name, Sort.mk_fun (List.map pred.args ~f:snd @ [ T_real.SReal ])))

let subst tsub pred =
  let tsub = Map.remove_keys tsub (List.map ~f:fst pred.args) in
  { pred with body = Term.subst tsub pred.body }

let lookup preds tvar =
  match List.find preds ~f:(fun pred -> Stdlib.( = ) tvar pred.name) with
  | Some pred -> Some (pred.kind, pred.args, pred.body)
  | None -> None

let str_of pred =
  sprintf "%s%s: real =%s %s;"
    (Ident.name_of_tvar pred.name)
    (if List.length pred.args > 0 then
       " " ^ str_of_sort_env_list Term.str_of_sort pred.args
     else "")
    (Predicate.str_of_fop pred.kind)
    (Term.str_of pred.body)

let str_of_ pred =
  sprintf "%s(%s) =%s %s"
    (Ident.name_of_tvar pred.name)
    (String.concat_map_list ~sep:"," ~f:(fst >> Ident.name_of_tvar) pred.args)
    (Predicate.str_of_fop pred.kind)
    (Term.str_of pred.body)

let str_of_list = String.concat_map_list ~sep:"\n" ~f:str_of
let pr_list ppf preds = Format.fprintf ppf "%s" (str_of_list preds)
let simplify pred = { pred with body = Evaluator.simplify_term pred.body }
