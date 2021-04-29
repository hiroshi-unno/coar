open Core
open Ast
open Ast.LogicOld

module Sexp = Ppx_sexp_conv_lib.Sexp

let str_of_binop op = let open Formula in
  match op with
  | And -> "and"
  | Or -> "or"
  | Imply -> "imply"
  | Iff -> "iff"

let str_of_binder binder = let open Formula in
  match binder with
  | Forall -> "forall"
  | Exists -> "exists"
  | Random r -> Rand.str_of r

let str_of_sort = function
  | T_bool.SBool -> "bool"
  | T_int.SInt -> "int"
  | T_real.SReal -> "real"
  | _ -> failwith "invalid sort"

let str_of_fixpoint = function
  | Predicate.Mu -> "mu"
  | Predicate.Nu -> "nu"

let rec sexp_of_formula phi = let open Formula in
  match phi with
  | Atom (atom, _) ->
    let atom = sexp_of_atom atom in
    Sexp.List [Sexp.Atom "atom"; atom]
  | UnaryOp (Not, phi, _) ->
    let phi = sexp_of_formula phi in
    Sexp.List [Sexp.Atom "not"; phi]
  | BinaryOp (op, phi1, phi2, _) ->
    let op = str_of_binop op in
    let phi1 = sexp_of_formula phi1 in
    let phi2 = sexp_of_formula phi2 in
    Sexp.List [Sexp.Atom op; phi1; phi2]
  | Bind (binder, params, phi, _) ->
    let binder = str_of_binder binder in
    let params = sexp_of_params params in
    let phi = sexp_of_formula phi in
    Sexp.List [Sexp.Atom binder; params; phi]
  | LetRec (bounded, phi, _) ->
    let bounded = List.map bounded ~f:(fun (fp, pvar, params, phi) -> sexp_of_pred @@ Predicate.Fixpoint (fp, pvar, params, phi) ) in
    let phi = sexp_of_formula phi in
    Sexp.List [Sexp.Atom "letrec"; Sexp.List bounded; phi]
and sexp_of_atom atom = let open Atom in
  match atom with
  | True _ -> Sexp.Atom "true"
  | False _ -> Sexp.Atom "false"
  | App (pred, args, _) ->
    let pred = sexp_of_pred pred in
    let args = sexp_of_args args in
    Sexp.List [Sexp.Atom "predapp"; pred; args]
and sexp_of_params params =
  let rec aux = function
    | [] -> []
    | (Ident.Tvar ident, sort)::xs ->
      let param = Sexp.List [Sexp.Atom ident; Sexp.Atom (str_of_sort sort)] in
      param :: (aux xs)
  in
  Sexp.List (aux (SortEnv.list_of params))

and sexp_of_args args =
  let rec aux = function
    | [] -> []
    | t :: ts -> (sexp_of_term t) :: (aux ts)
  in
  Sexp.List (aux args)
and sexp_of_term t = let open Term in
  match t with
  | Var (Ident.Tvar ident, sort, _) ->
    Sexp.List [Sexp.Atom ident; Sexp.Atom (str_of_sort sort)]
  | FunApp (T_bool.IfThenElse, [cond; then_; else_], _) ->
    let cond = sexp_of_term cond in
    let then_ = sexp_of_term then_ in
    let else_ = sexp_of_term else_ in
    Sexp.List [Sexp.Atom "if-then-else"; cond; then_; else_]
  | FunApp (sym, args, _) ->
    let sym = sexp_of_fun_sym sym in
    let args = sexp_of_args args in
    Sexp.List [Sexp.Atom "funapp"; sym; args]

and sexp_of_fun_sym = function
  | T_bool.Formula (Formula.Atom (atom, _)) ->
    let atom = sexp_of_atom atom in
    Sexp.List [Sexp.Atom "boolean"; atom]
  | T_int.Int n ->
    Sexp.List [Sexp.Atom "integer"; Sexp.Atom (Z.to_string n)]
  | T_int.Add -> Sexp.Atom "add"
  | T_int.Sub -> Sexp.Atom "sub"
  | T_int.Mult -> Sexp.Atom "mult"
  | T_int.Div -> Sexp.Atom "div"
  | T_int.Mod -> Sexp.Atom "mod"
  | T_int.Neg -> Sexp.Atom "neg"
  | _ -> failwith "invalid function symbol"

and sexp_of_pred_sym = function
  | T_bool.Eq -> Sexp.Atom "eq"
  | T_bool.Neq -> Sexp.Atom "neq"
  | T_int.Leq -> Sexp.Atom "leq"
  | T_int.Geq -> Sexp.Atom "geq"
  | T_int.Lt -> Sexp.Atom "lt"
  | T_int.Gt -> Sexp.Atom "gt"
  | _ -> failwith "invalid predicate symbol"

and sexp_of_pred pred = let open Predicate in
  match pred with
  | Var (Ident.Pvar ident, sorts) ->
    let sorts = List.map ~f:(fun sort -> Sexp.Atom (str_of_sort sort)) sorts in
    Sexp.List [Sexp.Atom ident; Sexp.List sorts]
  | Psym sym -> sexp_of_pred_sym sym
  | Fixpoint (fp, Ident.Pvar ident, params, phi) ->
    let fp = str_of_fixpoint fp in
    let params = sexp_of_params params in
    let phi = sexp_of_formula phi in
    Sexp.List [Sexp.Atom fp; Sexp.Atom ident; params; phi]

let str_of_formula phi =
  Sexp.to_string_hum (sexp_of_formula phi)

let str_of_pred pred =
  Sexp.to_string_hum (sexp_of_pred pred)

let str_of_atom atom =
  Sexp.to_string_hum (sexp_of_atom atom)
