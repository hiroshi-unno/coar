(* Printing of answers in the SyGuS output format: a solution as one
   [define-fun] per synthesised predicate (simplified first, with
   disequalities expanded since the format has none), and the [fail] or
   [infeasible] lines that the selected version of the format uses for an
   unsatisfiable or undecided problem. *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

type mode = SyGuS_IF1 | SyGuS_IF2

let mode = SyGuS_IF1

let rec str_of_sort = function
  | T_int.SInt -> "Int"
  | T_bool.SBool -> "Bool"
  | T_array.SArray (index, value) ->
      sprintf "(Array %s %s)" (str_of_sort index) (str_of_sort value)
  | s ->
      failwith (sprintf "[str_of_sort] %s not supported" (Term.str_of_sort s))

(* Generated identifiers contain '#'; quote names at both binding and use sites.
   SMT-LIB has no escape for a bar or backslash inside a quoted symbol. *)
let str_of_ident name =
  if String.exists name ~f:(fun c -> Char.equal c '|' || Char.equal c '\\') then
    failwith "identifier cannot be represented as an SMT-LIB quoted symbol"
  else "|" ^ name ^ "|"

let str_of_params params =
  String.concat_map_list ~sep:" " params ~f:(fun (Ident.Tvar name, sort) ->
      sprintf "(%s %s)" (str_of_ident name) (str_of_sort sort))

let rec str_of_formula = function
  | Formula.Atom (atom, _) -> str_of_atom atom
  | Formula.UnaryOp (Not, phi, _) -> sprintf "(not %s)" (str_of_formula phi)
  | Formula.BinaryOp (And, phi1, phi2, _) ->
      sprintf "(and %s %s)" (str_of_formula phi1) (str_of_formula phi2)
  | Formula.BinaryOp (Or, phi1, phi2, _) ->
      sprintf "(or %s %s)" (str_of_formula phi1) (str_of_formula phi2)
  | Formula.BinaryOp (Imply, phi1, phi2, _) ->
      sprintf "(=> %s %s)" (str_of_formula phi1) (str_of_formula phi2)
  | Formula.BinaryOp (Iff, _, _, _) -> failwith "'Iff' is not supported yet"
  | Formula.BinaryOp (Xor, _, _, _) -> failwith "'Xor' is not supported yet"
  | Formula.Bind (Forall, params, phi, _) ->
      sprintf "(forall (%s) %s)"
        (str_of_params params)
        (str_of_formula phi)
  | Formula.Bind (Exists, params, phi, _) ->
      sprintf "(exists (%s) %s)"
        (str_of_params params)
        (str_of_formula phi)
  | Formula.Bind (Random _, _, _, _) -> failwith "'Random' is not supported"
  | Formula.LetRec (_, _, _) -> failwith "'LetRec' is not supported yet"
  | Formula.LetFormula _ -> failwith "'LetFormula' is not supported yet"

and str_of_atom = function
  | Atom.True _ -> "true"
  | Atom.False _ -> "false"
  | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) when T_bool.is_true t2 ->
      sprintf "%s" (str_of_term t1)
  | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) when T_bool.is_false t2
    ->
      sprintf "(not %s)" (str_of_term t1)
  | Atom.App (Predicate.Psym op, [ t1; t2 ], _) ->
      sprintf "(%s %s %s)" (str_of_psym op) (str_of_term t1) (str_of_term t2)
  | Atom.App (pred, args, _) ->
      if List.length args = 0 then str_of_pred pred
      else
        sprintf "(%s %s)" (str_of_pred pred)
          (String.concat_map_list ~sep:" " ~f:str_of_term args)

and str_of_pred = function
  | Predicate.Var (Ident.Pvar _pvar, _sorts) ->
      failwith "predicate variable application not supported"
  (*sprintf "(%s : [%s])" pvar (String.concat_map_list ~sep:";" ~f:str_of_sort sorts)*)
  | Predicate.Psym sym -> str_of_psym sym
  | _ -> failwith "unsupported predicate symbol"

and str_of_term = function
  | Term.Var (Ident.Tvar tvar, _, _) -> str_of_ident tvar
  | Term.FunApp (T_bool.Formula phi, [], _) -> str_of_formula phi
  | Term.FunApp (T_bool.IfThenElse, [ cond; then_; else_ ], _) ->
      sprintf "(ite %s %s %s)" (str_of_term cond) (str_of_term then_)
        (str_of_term else_)
  | Term.FunApp (T_int.Int n, [], _) ->
      if Z.sign n < 0 then sprintf "(- %s)" (Z.to_string (Z.neg n))
      else Z.to_string n
  | Term.FunApp (T_real.Real _, [], _) -> failwith "real literal not supported"
  | Term.FunApp (T_array.ASelect _, [ array; index ], _) ->
      sprintf "(select %s %s)" (str_of_term array) (str_of_term index)
  | Term.FunApp (T_array.AStore _, [ array; index; value ], _) ->
      sprintf "(store %s %s %s)" (str_of_term array) (str_of_term index)
        (str_of_term value)
  | Term.FunApp (T_array.AConst (index, value), [ default ], _) ->
      sprintf "((as const %s) %s)" (str_of_sort (T_array.SArray (index, value)))
        (str_of_term default)
  | Term.FunApp (op, [ t1; t2 ], _) ->
      sprintf "(%s %s %s)" (str_of_funsym op) (str_of_term t1) (str_of_term t2)
  | Term.FunApp (T_int.Neg, [ t ], _) -> (
      match mode with
      | SyGuS_IF1 -> sprintf "(- 0 %s)" (str_of_term t)
      | SyGuS_IF2 -> sprintf "(- %s)" (str_of_term t))
  | _ -> failwith "unknown function application"

and str_of_funsym = function
  | T_int.Neg -> "-"
  | T_int.Add -> "+"
  | T_int.Sub -> "-"
  | T_int.Mul -> "*"
  | T_int.Div Value.Euclidean -> "div"
  | T_int.Rem Value.Euclidean -> "mod"
  | T_int.Div _ | T_int.Rem _ ->
      failwith
        "[SyGuS printing] non-Euclidean integer division/remainder requires an \
         explicit encoding"
  (*| T_int.Power _ -> "pow"*)
  | T_bool.IfThenElse -> "ite"
  | _ -> failwith "unknown function symbol"

and str_of_psym = function
  | T_bool.Eq -> "="
  | T_int.Leq -> "<="
  | T_int.Geq -> ">="
  | T_int.Lt -> "<"
  | T_int.Gt -> ">"
  (* [@@] and not a bare [^]: [failwith "..." ^ s] applies [failwith] to the
     literal alone and never evaluates the concatenation, so the symbol the
     message is about was dropped *)
  | psym -> failwith @@ "unknown pred symbol " ^ Predicate.str_of_psym psym

let str_of_solution (params, sol) =
  if Fn.non Map.Poly.is_empty params && Set.is_empty sol then assert false
  else
    String.concat_map_set ~sep:"\n" sol
      ~f:(fun (Ident.Pvar ident, (params, formula)) ->
        sprintf "(define-fun %s (%s) Bool %s)" (str_of_ident ident)
          (str_of_params params)
        @@ str_of_formula @@ Formula.elim_neq
        (* T_bool.Neq is not supported by SyGuS-IF *)
        @@ Z3Smt.Z3interface.simplify ~id:None Map.Poly.empty
        (* TODO *) @@ Evaluator.simplify formula)

let str_of_unsat () =
  match mode with SyGuS_IF1 -> "(fail)" | SyGuS_IF2 -> "infeasible"

let str_of_unknown () =
  match mode with SyGuS_IF1 -> "(fail)" | SyGuS_IF2 -> "fail"

(*
open Core
open Common.Ext
open Ast
open Ast.Logic

module type TermType = sig
  val str_of_sym: sym -> string
  val arity_of_sym: sym -> int
  val str_of: term -> string
end

module ExtTerm : TermType = struct
  open ExtTerm

  let str_of_sym = function
    (* bool theory *)
    | True -> "true"
    | False -> "false"
    | And -> "and"
    | Or -> "or"
    | Not -> "not"
    | Imply -> "imply"
    | Iff -> "iff"
    | Xor -> "xor"
    | IfThenElse -> "ite"
    | Eq -> "="

    (* int theory *)
    | Int n -> Z.(if Compare.(<) n zero then "(- " ^ to_string (-n) ^ ")" else to_string n)
    | Add -> "+"
    | Sub | Neg -> "-"
    | Abs -> "abs"
    | Mul -> "*"
    | Div -> "div"
    | Rem -> "mod" (*ToDo*)

    (* lia theory *)
    | Leq -> "<="
    | Geq -> ">="
    | Lt -> "<"
    | Gt -> ">"

    | _ -> failwith "unknown symbol"

  let arity_of_sym = ExtTerm.arity_of_sym

  let str_of = ExtTerm.str_of
end

module Make (Term : TermType) : sig
  val str_of_term: sort_env_map -> term -> string
end = struct
  let rec str_of_term map term : string = let open Ast.Logic.Term in
    if is_var term then let_var term |> fst |> Ident.name_of_tvar
    else if is_con term then let_con term |> fst |> Term.str_of_sym
    else if is_app term then let t1, t2, _ = let_app term in str_of_app map t1 t2
    else if is_tyapp term then let t, _, _ = let_tyapp term in str_of_term map t
    else failwith @@ sprintf "[str_of_term] not supported: %s" @@ Term.str_of term
  and str_of_app map t1 t2 = let open Ast.Logic.Term in
    let rec inner t1 t2 n =
      if is_var t1 then
        let v, _ = let_var t1 in
        match Map.Poly.find map v with
        | Some sort ->
          if n <> Sort.arity_of sort then
            failwith "the number of arguments is fewer/more than expected"
          else Ident.name_of_tvar v
        | None -> failwith @@ sprintf "unknown variable: %s" @@ Term.str_of t1
      else if is_con t1 then
        let sym, _ = let_con t1 in
        if n <> Term.arity_of_sym sym then
          failwith "the number of arguments is fewer/more than expected"
        else Term.str_of_sym sym
      else if is_tyapp t1 then
        let t, _, _ = let_tyapp t1 in inner t t2 n
      else if is_app t1 then
        let t11, t12, _ = let_app t1 in
        sprintf "%s %s" (inner t11 t12 (n + 1)) (str_of_term map t2)
      else failwith @@ sprintf "[str_of_app] not supported: %s" @@ Term.str_of t1
    in
    String.paren @@ inner t1 t2 0
end
*)
