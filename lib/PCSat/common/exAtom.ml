open Core
open Common.Util
open Ast
open Ast.LogicOld

type pred = SortMap.t * Formula.t
type papp = (Ident.pvar * Sort.t list) * Term.t list
type ppapp = pred * papp
type t =
  | FCon of pred
  | PApp of papp (* non-parametric atom *) (* assume that papp is ground *)
  | PPApp of ppapp (* parametric atom *)

let mk_fcon pred = FCon pred
let mk_true () = mk_fcon (Map.Poly.empty, Formula.mk_true ())
let mk_false () = mk_fcon (Map.Poly.empty, Formula.mk_false ())
let mk_papp pvar sorts args = PApp ((pvar, sorts), args)
let mk_ppapp pred pvar sorts args = PPApp (pred, ((pvar, sorts), args))

let of_old_atom exi_senv cond = function
  | Atom.App (Predicate.Var(pvar, sorts), terms, _) ->
    let param_senv = Set.Poly.union_list @@
      Formula.sort_env_of cond :: List.map ~f:Term.sort_env_of terms in
    if Set.Poly.is_empty param_senv then mk_papp pvar sorts terms
    else mk_ppapp (Map.of_set @@ Set.Poly.filter ~f:(fun (x, _) -> not @@ Map.Poly.mem exi_senv x) param_senv, cond) pvar sorts terms
  | Atom.App (Psym _, _, _) as atom ->
    (try if Evaluator.eval_atom atom then mk_true () else mk_false () with _ ->
       let param_senv = Atom.sort_env_of atom in
       mk_fcon (Map.of_set @@ Set.Poly.filter ~f:(fun (x, _) -> not @@ Map.Poly.mem exi_senv x) param_senv, Formula.mk_atom atom))
  | _ -> failwith "only atoms can be converted into examples."
let of_atom cond exi_senv t = of_old_atom exi_senv cond @@ Logic.ExtTerm.to_old_atom exi_senv t []

let is_fcon = function FCon _ -> true | _ -> false
let is_papp = function PApp _ -> true | _ -> false
let is_ppapp = function PPApp _ -> true | _ -> false

let pvar_of = function PApp((pvar, _), _) | PPApp(_, ((pvar, _), _)) -> Some pvar | _ -> None
let sorts_of = function PApp((_, sorts), _) | PPApp(_, ((_, sorts), _)) -> Some sorts | _ -> None
let tvs_of = function
  | FCon (_, phi) -> Formula.tvs_of phi
  | PApp((_, _), ts) -> assert (List.for_all ts ~f:(fun t -> Set.Poly.is_empty @@ Term.tvs_of t)); Set.Poly.empty
  | PPApp((_, phi), ((_, _), ts)) -> Set.Poly.union_list (Formula.tvs_of phi :: List.map ~f:Term.tvs_of ts)
let args_of = function
  | FCon (_, _) -> None
  | PApp((_, _), ts) -> Some ts
  | PPApp((_, _), ((_, _), ts)) -> Some ts
let params_of = function
  | FCon (param_senv, _) -> param_senv
  | PApp (_, _) -> Map.Poly.empty
  | PPApp ((param_senv, _), _) -> param_senv

let rename map = function
  | FCon (params, phi) ->
    FCon (Map.rename_keys params ~f:(Map.Poly.find map), Formula.rename map phi)
  | PApp((pvar, sorts), ts) ->
    PApp((pvar, sorts), List.map ~f:(Term.rename map) ts)
  | PPApp((params, phi), ((pvar, sorts), ts)) ->
    PPApp((Map.rename_keys params ~f:(Map.Poly.find map), Formula.rename map phi),
          ((pvar, sorts), List.map ~f:(Term.rename map) ts))

let to_old_atom = function
  | FCon (_, phi) ->
    if Formula.is_true phi then Some (Map.Poly.empty, Atom.mk_true ())
    else if Formula.is_false phi then Some (Map.Poly.empty, Atom.mk_false ())
    else None (*ToDo*)
  | PApp ((pvar, sorts), terms) -> Some (Map.Poly.empty, Atom.mk_app (Predicate.mk_var pvar sorts) terms)
  | PPApp ((param_senv, phi), ((pvar, sorts), terms)) ->
    if Formula.is_true phi then Some (param_senv, Atom.mk_app (Predicate.mk_var pvar sorts) terms) else None(*ToDo*)
let to_atom atm =
  match to_old_atom atm with
  | None -> None
  | Some (param_senv, atm) -> Some (param_senv, Logic.ExtTerm.of_old_atom atm)
let to_old_formula pos = function
  | FCon (param_senv, phi) ->
    param_senv, (if pos then ident else Formula.mk_neg ~info:Dummy) @@ phi
  | PApp ((pvar, sorts), terms) ->
    Map.Poly.empty,
    (if pos then ident else Formula.mk_neg ~info:Dummy) @@
    Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts terms
  | PPApp ((param_senv, phi), ((pvar, sorts), terms)) ->
    let papp = 
      (if pos then ident else Formula.mk_neg ~info:Dummy) @@
      Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts terms
    in
    param_senv, if Formula.is_true phi then papp else Formula.mk_imply phi papp
let to_formula pos atm =
  let param_senv, phi = to_old_formula pos atm in
  param_senv, Logic.ExtTerm.of_old_formula phi
let to_old_formula_and_cond  =function
  | FCon (param_senv, phi) ->
    param_senv, Formula.mk_true (), phi
  | PApp ((pvar, sorts), terms) ->
    Map.Poly.empty, Formula.mk_true (), Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts terms
  | PPApp ((param_senv, phi), ((pvar, sorts), terms)) ->
    param_senv, phi, Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts terms
let cond_map_of fenv cond =
  if Formula.is_true cond then Map.Poly.empty else
    match Z3Smt.Z3interface.check_sat fenv [cond] with
    | `Sat model -> 
      List.fold_left model ~init:Map.Poly.empty ~f:(
        fun ret ((tvar, _), term) -> match term with | None -> ret | Some t -> Map.Poly.set ret ~key:tvar ~data:(Logic.ExtTerm.of_old_term t))
    | _ -> Map.Poly.empty
let to_formula_and_cond fenv atm =
  let param_senv, cond, phi = to_old_formula_and_cond atm in
  param_senv, cond_map_of fenv cond, Logic.ExtTerm.of_old_formula phi

let str_of_papp ((Ident.Pvar ident, _), terms) =
  Printf.sprintf "%s(%s)"
    ident
    (String.concat ~sep:", " @@
     List.mapi ~f:(fun _i t -> (*Printf.sprintf "[x%d] %s" (i+1) @@*) Term.str_of t ~priority:Priority.comma) terms)
let str_of = function
  | FCon (_, phi) -> Formula.str_of phi
  | PApp papp -> str_of_papp papp
  | PPApp ((_, phi), papp) ->
    if Formula.is_true phi then Printf.sprintf "%s" (str_of_papp papp)
    else Printf.sprintf "(%s | %s)" (Formula.str_of phi) (str_of_papp papp)

let normalize_pred (param_senv, phi) = param_senv, Normalizer.normalize @@ Evaluator.simplify phi
let normalize_papp (target, terms) =
  target,
  List.map terms ~f:(fun term ->
      try Evaluator.eval_term term |> Term.of_value with _ ->
        Normalizer.normalize_term @@ Evaluator.simplify_term term(*ToDo: check*))
let normalize = function
  | FCon pred -> FCon (normalize_pred pred)
  | PApp papp -> PApp (normalize_papp papp)
  | PPApp (pred, papp) -> PPApp(normalize_pred pred, normalize_papp papp)

let instantiate = function
  | FCon (param_senv, phi) ->
    let sub = Map.Poly.map param_senv ~f:T_dt.mk_dummy(*ToDo: find one that satisfies phi?*) in
    FCon (Map.Poly.empty, Formula.subst sub phi)
  | PApp papp -> PApp papp
  | PPApp ((param_senv, phi), (target, terms)) ->
    let sub = Map.Poly.mapi param_senv ~f:(
        fun ~key:_ ~data ->  T_dt.mk_dummy data)(*ToDo: find one that satisfies phi*) in
    let phi = Formula.subst sub phi in
    let terms = List.map terms ~f:(Term.subst sub) in
    try
      if Evaluator.eval phi then
        PApp (target, List.map terms ~f:(fun t -> Term.of_value @@ Evaluator.eval_term @@ t))
      else PPApp ((Map.Poly.empty, Formula.mk_false ()), (target, terms))
    with _ -> PPApp ((Map.Poly.empty, phi), (target, terms))

let iterate_vars tvs = function
  | FCon (params, phi) ->
    let s = Set.Poly.of_list @@ Map.Poly.keys params in
    (Set.Poly.to_list @@ Set.Poly.inter s @@ Set.Poly.diff (Formula.fvs_of phi) (Set.Poly.of_list tvs)) @ tvs
  | PApp(_, _) -> tvs
  | PPApp((params, phi), (_, ts)) ->
    let s = Set.Poly.of_list @@ Map.Poly.keys params in
    let tvs =
      List.fold_left ts ~init:tvs ~f:(fun tvs t ->
          (Set.Poly.to_list @@ Set.Poly.inter s @@ Set.Poly.diff (Term.tvs_of t) (Set.Poly.of_list tvs)) @ tvs)
    in
    (Set.Poly.to_list @@ Set.Poly.inter s @@ Set.Poly.diff (Formula.fvs_of phi) (Set.Poly.of_list tvs)) @ tvs

let normalize_params atm =
  let tvs = iterate_vars [] atm in
  let map = Map.Poly.of_alist_exn @@
    List.mapi tvs ~f:(fun i x -> x, Ident.mk_dontcare (string_of_int (i+1))) in
  rename map atm
