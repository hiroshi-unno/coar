open Core
open Ast
open Ast.Logic

module type TermType = sig
  val str_of_sym: sym -> string
  val arity_of_sym: sym -> int
  val str_of: Logic.term -> string
end

module ExtTerm : TermType = struct
  open Logic.ExtTerm

  let str_of_sym = function
    (* bool theory *)
    | True -> "true"
    | False -> "false"
    | And -> "and"
    | Or -> "or"
    | Not -> "not"
    | Imply -> "imply"
    | Xor -> "xor"
    | Iff -> "iff"
    | IfThenElse -> "ite"
    | Eq -> "="

    (* int theory *)
    | Int n -> Z.(if Compare.(<) n zero then "(- " ^ to_string (-n) ^ ")" else to_string n)
    | Add -> "+"
    | Sub | Neg -> "-"
    | Mult -> "*"
    | Div -> "div"
    | Mod -> "mod"
    | Abs -> "abs"

    (* lia theory *)
    | Leq -> "<="
    | Geq -> ">="
    | Lt -> "<"
    | Gt -> ">"

    | _ -> failwith "unknown symbol"

  let arity_of_sym = Logic.ExtTerm.arity_of_sym 

  let str_of = Logic.ExtTerm.str_of
end

module Make (Term : TermType) : sig
  val str_of_term: Logic.SortMap.t -> Logic.term -> string
end = struct
  let rec str_of_term map term : string = let open Logic.Term in
    if is_var term then let v, _ = let_var term in match v with Ident.Tvar v -> v
    else if is_con term then let sym, _ = let_con term in Term.str_of_sym sym
    else if is_app term then let t1, t2, _ = let_app term in str_of_app map t1 t2
    else if is_tyapp term then let t, _, _ = let_tyapp term in str_of_term map t
    else failwith @@ Printf.sprintf "it is not supported yet : %s" @@ Term.str_of term

  and str_of_app map t1 t2 = let open Logic.Term in
    let rec inner t1 t2 n =
      if is_var t1 then let v, _ = let_var t1 in
        match Logic.SortMap.find map v with
        | Some sort ->
          if not (n = Sort.arity_of sort) then failwith "the number of arguments is fewer/more than expected" else
            begin match v with Ident.Tvar v -> v end
        | None -> failwith @@ Printf.sprintf "unknown var : %s" @@ Term.str_of t1
      else if is_con t1 then let sym, _ = let_con t1 in
        if not (n = Term.arity_of_sym sym) then failwith "the number of arguments is fewer/more than expected" else
          Term.str_of_sym sym
      else if is_tyapp t1 then let t, _, _ = let_tyapp t1 in inner t t2 n
      else if is_app t1 then let t11, t12, _ = let_app t1 in Printf.sprintf "%s %s" (inner t11 t12 (n+1)) (str_of_term map t2)
      else failwith @@ Printf.sprintf "it is not supported yet : %s" @@ Term.str_of t1
    in Printf.sprintf "(%s)" @@ inner t1 t2 0
end
