open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

type t = {
  kind : Predicate.fixpoint;
  name : Ident.pvar;
  args : sort_env_list;
  body : Formula.t;
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
  let atm = Formula.mk_atom @@ Atom.pvar_app_of_senv pred.name pred.args in
  match pred.kind with
  | Predicate.Mu -> Formula.mk_imply pred.body atm
  | Predicate.Nu -> Formula.mk_imply atm pred.body
  | Predicate.Fix -> failwith "to_formula"

let sort_env_of_list preds =
  Set.Poly.of_list @@ Logic.of_old_sort_env_list
  @@ List.map preds ~f:(fun pred ->
         Term.pred_to_sort_bind (pred.name, List.map pred.args ~f:snd))

let subst tsub pred =
  let tsub = Map.remove_keys tsub (List.map ~f:fst pred.args) in
  { pred with body = Formula.subst tsub pred.body }

let lookup preds pvar =
  match List.find preds ~f:(fun pred -> Stdlib.( = ) pvar pred.name) with
  | Some pred -> Some (pred.kind, pred.args, pred.body)
  | None -> None

let str_of pred =
  sprintf "%s%s: bool =%s %s;"
    (Ident.name_of_pvar pred.name)
    (if List.length pred.args > 0 then
       " " ^ str_of_sort_env_list Term.str_of_sort pred.args
     else "")
    (Predicate.str_of_fop pred.kind)
    (Formula.str_of pred.body)

let str_of_ pred =
  sprintf "%s(%s) =%s %s"
    (Ident.name_of_pvar pred.name)
    (String.concat_map_list ~sep:"," ~f:(fst >> Ident.name_of_tvar) pred.args)
    (Predicate.str_of_fop pred.kind)
    (Formula.str_of pred.body)

let str_of_list = String.concat_map_list ~sep:"\n" ~f:str_of
let pr_list ppf preds = Format.fprintf ppf "%s" (str_of_list preds)

let replace_app_add formula arg sort =
  Formula.map_atom formula ~f:(function
    | Atom.App (Predicate.Var (pvar, arg_sorts), args, info) ->
        Formula.mk_atom
        @@ Atom.mk_pvar_app ~info pvar (sort :: arg_sorts) (arg :: args)
    | atm -> Formula.mk_atom atm)

let elim_mu_with_rec preds tvar_rec =
  List.map preds ~f:(fun pred ->
      let term = Term.mk_var tvar_rec T_int.SInt in
      let body =
        if Stdlib.( = ) pred.kind Predicate.Nu then
          replace_app_add pred.body term T_int.SInt
        else
          (* replace all F X Y with F (rec_ - 1) X Y *)
          let term = Term.mk_fsym_app T_int.Sub [ term; T_int.one () ] in
          let body = replace_app_add pred.body term T_int.SInt in
          (* body --> rec_ > 0 /\ body *)
          Formula.mk_and (Formula.gt term (T_int.zero ())) body
      in
      {
        pred with
        kind = Predicate.Nu;
        args = (tvar_rec, T_int.SInt) :: pred.args;
        body;
      })
