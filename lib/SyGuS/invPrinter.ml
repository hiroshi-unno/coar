open Core
open Ast.LogicOld
open Ast

type mode = SyGuS_IF1 | SyGuS_IF2

let mode = SyGuS_IF1

let str_of_sort = function
  | T_int.SInt -> "Int"
  | T_bool.SBool -> "Bool"
  | s -> failwith (Term.str_of_sort s ^ " not supported")

let str_of_sort_env senv =
  String.concat ~sep:" " @@
  List.map ~f:(fun (tvar, sort) ->
      Printf.sprintf "(%s %s)" (Ident.name_of_tvar tvar) (str_of_sort sort)) @@
  LogicOld.SortEnv.list_of senv

let rec str_of_formula phi = let open Formula in
  match phi with
  | Atom (atom, _) -> str_of_atom atom
  | UnaryOp (Not, phi, _) -> Printf.sprintf "(not %s)" (str_of_formula phi)
  | BinaryOp (And, phi1, phi2, _) ->
    Printf.sprintf "(and %s %s)" (str_of_formula phi1) (str_of_formula phi2)
  | BinaryOp (Or, phi1, phi2, _) ->
    Printf.sprintf "(or %s %s)" (str_of_formula phi1) (str_of_formula phi2)
  | BinaryOp (Imply, phi1, phi2, _) ->
    Printf.sprintf "(=> %s %s)" (str_of_formula phi1) (str_of_formula phi2)
  | BinaryOp (Iff, _, _, _) -> failwith "'Iff' is not supported yet"
  | Bind (Forall, params, phi, _) ->
    Printf.sprintf "(forall (%s) %s)" (str_of_sort_env params) (str_of_formula phi)
  | Bind (Exists, params, phi, _) ->
    Printf.sprintf "(exists (%s) %s)" (str_of_sort_env params) (str_of_formula phi)
  | Bind (Random _, _, _, _) -> failwith "'Random' is not supported"
  | LetRec (_, _, _) -> failwith "'LetRec' is not supported yet"
and str_of_atom atom = let open Atom in
  match atom with
  | True _ -> "true"
  | False _ -> "false"
  | App (Predicate.Psym op, [t1; t2], _) ->
    Printf.sprintf "(%s %s %s)" (str_of_predsym op) (str_of_term t1) (str_of_term t2)
  | App (pred, args, _) ->
    if List.length args = 0 then
      str_of_pred pred
    else
      Printf.sprintf "(%s %s)"
        (str_of_pred pred)
        (String.concat ~sep:" " @@ List.map ~f:str_of_term args)
and str_of_pred pred = let open Predicate in
  match pred with
  | Var (Ident.Pvar _pvar, _sorts) -> 
    failwith "predicate variable application not supported"
  (*Printf.sprintf "(%s : [%s])" pvar (String.concat ~sep:";" @@ List.map ~f:str_of_sort sorts)*)
  | Psym sym -> str_of_predsym sym
  | _ -> failwith "unsupported predicate symbol"
and str_of_term = function
  | Term.Var (Ident.Tvar tvar, _, _) -> tvar
  | Term.FunApp (T_bool.Formula phi, [], _) -> str_of_formula phi
  | Term.FunApp (T_bool.IfThenElse, [cond; then_; else_], _) ->
    Printf.sprintf "(ite %s %s %s)" (str_of_term cond) (str_of_term then_) (str_of_term else_)
  | Term.FunApp (T_int.Int n, [], _) ->
    (match mode with
     | SyGuS_IF1 -> Z.to_string n
     | SyGuS_IF2 -> Z.(if Compare.(<) n zero then "(- " ^ to_string (-n) ^ ")" else to_string n))
  | Term.FunApp (T_real.Real _, [], _) -> failwith "real literal not supported"
  | Term.FunApp (op, [t1; t2], _) ->
    Printf.sprintf "(%s %s %s)" (str_of_funsym op) (str_of_term t1) (str_of_term t2)
  | Term.FunApp (T_int.Neg, [t], _) ->
    (match mode with
     | SyGuS_IF1 -> Printf.sprintf "(0 - %s)" (str_of_term t)
     | SyGuS_IF2 -> Printf.sprintf "(- %s)" (str_of_term t))
  | _ -> failwith "unknown function application"
and str_of_funsym = function
  | T_int.Add -> "+"
  | T_int.Sub -> "-"
  | T_int.Mult -> "*"
  | T_int.Div -> "div"
  | T_int.Mod -> "mod"
  | T_int.Neg -> "-"
  | T_bool.IfThenElse -> "ite"
  | _ -> failwith "unknown function symbol"
and str_of_predsym = function
  | T_bool.Eq -> "="
  | T_int.Leq -> "<="
  | T_int.Geq -> ">="
  | T_int.Lt -> "<"
  | T_int.Gt -> ">"
  | _ -> failwith "unknown pred symbol"

let str_of_solution (params, sol) =
  let fenv = Set.Poly.empty in
  if not @@ Map.Poly.is_empty params && Set.Poly.is_empty sol then assert false
  else Set.Poly.to_list sol
       |> List.map ~f:(fun (Ident.Pvar ident, (params, formula)) ->
           let formula = Formula.elim_neq @@ Z3Smt.Z3interface.simplify fenv @@ Evaluator.simplify formula in
           Printf.sprintf "(define-fun %s (%s) Bool %s)" ident (str_of_sort_env params) (str_of_formula formula))
       |> String.concat ~sep:"\n"
