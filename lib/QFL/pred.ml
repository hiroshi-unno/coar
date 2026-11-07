(* One equation of a QFL (quantitative fixpoint logic) problem: a real-valued
   function defined as the least or greatest fixpoint of its body, with
   optional annotations and constraints on its arguments.  [to_formula]
   states the prefixed-point (for a least fixpoint) or postfixed-point (for a
   greatest one) inequality that a candidate must satisfy. *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

type t = {
  kind : Predicate.fixpoint;
  name : Ident.tvar;
  args : sort_env_list;
  body : Term.t;
  annots : Formula.t list;
  arg_constrs : Formula.t list;
}

let make ?(annots = []) ?(arg_constrs = []) kind name args body =
  { kind; name; args; body; annots; arg_constrs }

let map f pred = { pred with body = f pred.body }
let map_list f = List.map ~f:(map f)
let pvars_of_list = List.map ~f:(fun pred -> pred.name)

let fvs_of pred =
  Set.diff (Term.fvs_of pred.body)
    (Set.Poly.of_list @@ List.map pred.args ~f:fst)

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
  | Predicate.MuOrNu -> failwith "to_formula"

let sort_env_of_list preds =
  Set.Poly.of_list @@ Logic.of_old_sort_env_list
  @@ List.map preds ~f:(fun pred ->
      (pred.name, Sort.mk_fun (List.map pred.args ~f:snd @ [ T_real.SReal ])))

let subst tsub pred =
  let tsub = Map.remove_keys tsub (List.map pred.args ~f:fst) in
  let free = Lazy.force (Term.range_fvs tsub) in
  if not (List.exists pred.args ~f:(fun (var, _) -> Set.mem free var)) then
    { pred with body = Term.subst tsub pred.body }
  else
    (* Reconstruct the formal scope for capture-avoiding substitution. The
     nonnullary carrier contains the body and metadata only to make the common
     binder traversal see their names; it never escapes to a solver/output.
     Metadata keeps its existing contract: alpha-renaming only, not [tsub]. *)
    let terms =
      pred.body
      :: List.map (pred.annots @ pred.arg_constrs) ~f:T_bool.of_formula
    in
    let carrier =
      Formula.mk_atom
        (Atom.mk_pvar_app (Ident.Pvar "qfl_substitution_scope_carrier")
           (List.map terms ~f:Term.sort_of)
           terms)
    in
    match Formula.subst tsub (Formula.mk_forall pred.args carrier) with
    | Formula.Bind
        (Forall, args, Formula.Atom (Atom.App (_, body :: _, _), _), _) ->
        let ren =
          List.map2_exn pred.args args ~f:(fun (old, sort) (fresh, _) ->
              if Stdlib.(old = fresh) then None
              else Some (old, Term.mk_var fresh sort))
          |> List.filter_opt |> Map.Poly.of_alist_exn
        in
        {
          pred with
          args;
          body;
          annots = List.map pred.annots ~f:(Formula.subst ren);
          arg_constrs = List.map pred.arg_constrs ~f:(Formula.subst ren);
        }
    | _ -> assert false

let subst_funcs fsub pred =
  let fsub = Map.remove fsub pred.name in
  if Map.Poly.is_empty fsub || List.is_empty pred.args then
    { pred with body = Term.subst_funcs fsub pred.body }
  else
    (* As in [subst], the formals scope the detached body. Include metadata in
       the temporary carrier so fresh formals cannot collide with its names;
       metadata receives only the resulting alpha change. *)
    let terms =
      pred.body
      :: List.map (pred.annots @ pred.arg_constrs) ~f:T_bool.of_formula
    in
    let carrier =
      Formula.mk_atom
        (Atom.mk_pvar_app (Ident.Pvar "qfl_function_substitution_scope_carrier")
           (List.map terms ~f:Term.sort_of)
           terms)
    in
    let args, carrier, fsub =
      Term.scope_func_subst fsub pred.args (T_bool.of_formula carrier)
    in
    match Formula.of_bool_term carrier with
    | Formula.Atom (Atom.App (_, body :: metadata, _), _) ->
        let metadata = List.map metadata ~f:Formula.of_bool_term in
        let annots, arg_constrs =
          List.split_n metadata (List.length pred.annots)
        in
        {
          pred with
          args;
          body = Term.subst_funcs fsub body;
          annots;
          arg_constrs;
        }
    | _ -> assert false

let lookup preds tvar =
  match List.find preds ~f:(fun pred -> Stdlib.( = ) tvar pred.name) with
  | Some pred -> Some (pred.kind, pred.args, pred.body)
  | None -> None

let str_of pred =
  sprintf "%s %s : real =%s %s;"
    (Ident.name_of_tvar pred.name)
    (if List.length pred.args > 0 then
       str_of_sort_env_list Term.str_of_sort pred.args
     else "")
    (Predicate.str_of_fop pred.kind)
    (Term.str_of pred.body)

let str_of_list = String.concat_map_list ~sep:"\n" ~f:str_of
let pr_list ppf preds = Format.fprintf ppf "%s" (str_of_list preds)
let simplify pred = { pred with body = Evaluator.simplify_term pred.body }
let normalize pred = { pred with body = Normalizer.normalize_term pred.body }
