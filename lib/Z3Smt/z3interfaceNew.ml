open Core
open Z3
open Ast
open Ast.Logic

let of_var ctx (Ident.Tvar var) = var |> String.escaped |> Symbol.mk_string ctx

module type TermType = sig
  (* our Term to Z3 Expr *)
  val of_sort : context -> Sort.t -> Z3.Sort.sort
  val of_nullary_con : context -> sym -> Z3.Expr.expr
  val of_con : context -> Expr.expr list -> sym -> Z3.Expr.expr

  (* Z3 Expr to our Term *)
  val nullary_con_of : Z3.Expr.expr -> Logic.term option

  val con_of :
    (Logic.term -> Z3.Expr.expr -> Logic.term) ->
    Z3.Expr.expr ->
    Logic.term option
end

module BoolTerm : TermType = struct
  open BoolTerm

  let of_sort ctx = function
    | SBool -> Boolean.mk_sort ctx
    | _ -> failwith "unknown sort"

  let of_nullary_con ctx = function
    | True -> Boolean.mk_true ctx
    | False -> Boolean.mk_false ctx
    | _ -> failwith "the symbol is not nullary"

  let of_con ctx args = function
    | And -> Boolean.mk_and ctx args
    | Or -> Boolean.mk_or ctx args
    | Not -> (
        match args with
        | exp :: [] -> Boolean.mk_not ctx exp
        | _ -> assert false)
    | Imply -> (
        match args with
        | [ exp1; exp2 ] -> Boolean.mk_or ctx [ Boolean.mk_not ctx exp1; exp2 ]
        | _ -> assert false)
    | Iff -> (
        match args with
        | [ exp1; exp2 ] -> Boolean.mk_eq ctx exp1 exp2
        | _ -> assert false)
    | Xor -> (
        match args with
        | [ exp1; exp2 ] -> Boolean.mk_not ctx @@ Boolean.mk_eq ctx exp1 exp2
        | _ -> assert false)
    | IfThenElse -> (
        match args with
        | [ exp1; exp2; exp3 ] -> Boolean.mk_ite ctx exp1 exp2 exp3
        | _ -> assert false)
    | Eq -> (
        match args with
        | [ exp1; exp2 ] -> Boolean.mk_eq ctx exp1 exp2
        | _ -> assert false)
    | Neq -> (
        match args with
        | [ exp1; exp2 ] -> Boolean.mk_not ctx @@ Boolean.mk_eq ctx exp1 exp2
        | _ -> assert false)
    | _ -> assert false

  let nullary_con_of expr =
    if Boolean.is_true expr then BoolTerm.mk_bool true |> Option.some
    else if Boolean.is_false expr then BoolTerm.mk_bool false |> Option.some
    else None

  let con_of mk_op_app expr =
    let term =
      if Boolean.is_and expr then mk_op_app (mk_and ()) expr
      else if Boolean.is_or expr then mk_op_app (mk_or ()) expr
      else if Boolean.is_not expr then mk_op_app (mk_not ()) expr
      else if Boolean.is_iff expr then mk_op_app (mk_iff ()) expr
      else if Boolean.is_implies expr then mk_op_app (mk_imply ()) expr
      else if Boolean.is_ite expr then mk_op_app (mk_bool_ite ()) expr
      else if Boolean.is_eq expr then mk_op_app (mk_bool_eq ()) expr
      else assert false
    in
    Option.some term
end

module IntTerm : TermType = struct
  open IntTerm

  let of_sort ctx = function
    | SInt -> Arithmetic.Integer.mk_sort ctx
    | _ -> failwith "unknown sort"

  let of_nullary_con ctx = function
    | Int n -> Arithmetic.Integer.mk_numeral_s ctx (Z.to_string n)
    | _ -> failwith "the symbol is not nullary"

  let of_con ctx args = function
    | Neg -> (
        match args with
        | exp :: [] -> Arithmetic.mk_unary_minus ctx exp
        | _ -> assert false)
    | Add -> Arithmetic.mk_add ctx args
    | Sub -> Arithmetic.mk_sub ctx args
    | Mult -> Arithmetic.mk_mul ctx args
    | Div -> (
        match args with
        | [ exp1; exp2 ] -> Arithmetic.mk_div ctx exp1 exp2
        | _ -> assert false)
    | Mod -> (
        match args with
        | [ exp1; exp2 ] -> Arithmetic.Integer.mk_mod ctx exp1 exp2
        | _ -> assert false)
    | _ -> assert false

  let nullary_con_of expr =
    if Arithmetic.is_int_numeral expr then
      mk_int (Arithmetic.Integer.get_big_int expr) |> Option.some
    else None

  let con_of mk_op_app expr =
    let term =
      if Arithmetic.is_add expr then mk_op_app (mk_add ()) expr
      else if Arithmetic.is_sub expr then mk_op_app (mk_sub ()) expr
      else if Arithmetic.is_mul expr then mk_op_app (mk_mult ()) expr
      else if Arithmetic.is_div expr || Arithmetic.is_idiv expr then
        mk_op_app (mk_div ()) expr
      else assert false
    in
    Option.some term
end

module RealTerm : TermType = struct
  open RealTerm

  let of_sort ctx = function
    | SReal -> Arithmetic.Real.mk_sort ctx
    | _ -> failwith "unknown sort"

  let of_nullary_con ctx = function
    | Real r -> Arithmetic.Real.mk_numeral_s ctx (Q.to_string r)
    | _ -> failwith "the symbol is not nullary"

  let of_con ctx args = function
    | RNeg -> (
        match args with
        | exp :: [] -> Arithmetic.mk_unary_minus ctx exp
        | _ -> assert false)
    | RAdd -> Arithmetic.mk_add ctx args
    | RSub -> Arithmetic.mk_sub ctx args
    | RMult -> Arithmetic.mk_mul ctx args
    | RDiv -> (
        match args with
        | [ exp1; exp2 ] ->
            Arithmetic.mk_div ctx
              (Arithmetic.Integer.mk_int2real (*ToDo: remove*) ctx exp1)
              (Arithmetic.Integer.mk_int2real (*ToDo: remove*) ctx exp2)
        | _ -> assert false)
    | _ -> assert false

  let nullary_con_of expr =
    if Arithmetic.is_real expr then
      mk_real (Arithmetic.Real.get_ratio expr) |> Option.some
    else None

  let con_of mk_op_app expr =
    Option.some
    @@
    if Arithmetic.is_add expr then mk_op_app (mk_radd ()) expr
    else if Arithmetic.is_sub expr then mk_op_app (mk_rsub ()) expr
    else if Arithmetic.is_mul expr then mk_op_app (mk_rmult ()) expr
    else if Arithmetic.is_div expr || Arithmetic.is_idiv expr then
      mk_op_app (mk_rdiv ()) expr
    else assert false
end

(* ToDo: support BVTerm *)

module IRBTerm : TermType = struct
  open IRBTerm

  let of_sort ctx = function
    | SInt -> Arithmetic.Integer.mk_sort ctx
    | SReal -> Arithmetic.Real.mk_sort ctx
    | SBV size -> BitVector.mk_sort ctx (BVTerm.bits_of size)
    | _ -> failwith "unknown sort"

  let of_nullary_con ctx = function
    | Int n -> Arithmetic.Integer.mk_numeral_s ctx (Z.to_string n)
    | Real r -> Arithmetic.Real.mk_numeral_s ctx (Q.to_string r)
    | BVNum (size, n) ->
        Z3.BitVector.mk_numeral ctx (Z.to_string n) (BVTerm.bits_of size)
    | _ -> failwith "the symbol is not nullary"

  let of_con ctx args = function
    | IntToReal -> (
        match args with
        | exp :: [] -> Arithmetic.Integer.mk_int2real ctx exp
        | _ -> assert false)
    | RealToInt -> (
        match args with
        | exp :: [] -> Arithmetic.Real.mk_real2int ctx exp
        | _ -> assert false)
    | IntToBV size -> (
        match args with
        | exp :: [] ->
            Arithmetic.Integer.mk_int2bv ctx (BVTerm.bits_of size) exp
        | _ -> assert false)
    | BVToInt size -> (
        match args with
        | exp :: [] -> Z3.BitVector.mk_bv2int ctx exp (BVTerm.signed_of size)
        | _ -> assert false)
    | sym ->
        if Map.Poly.mem Logic.IntTerm.sym_sort_map sym then
          IntTerm.of_con ctx args sym
        else if Map.Poly.mem Logic.RealTerm.sym_sort_map sym then
          RealTerm.of_con ctx args sym
        else assert false

  let nullary_con_of expr =
    match RealTerm.nullary_con_of expr with
    | Some x -> Some x
    | None -> IntTerm.nullary_con_of expr

  let con_of mk_op_app expr =
    let term =
      if Arithmetic.is_int2real expr then mk_op_app (mk_int_to_real ()) expr
      else if Arithmetic.is_real2int expr then
        mk_op_app (mk_real_to_int ()) expr
        (* convert to Term ignoring mismatch of sort of ite/eq
           The type will be checked after an ast is build *)
      else
        match RealTerm.con_of mk_op_app expr with
        | Some x -> x
        | None -> (
            match IntTerm.con_of mk_op_app expr with
            | Some x -> x
            | _ -> assert false)
    in
    Option.some term
end

module ExtTerm : TermType = struct
  open ExtTerm

  let of_sort ctx = function
    | SBool -> Boolean.mk_sort ctx
    | SReal -> Arithmetic.Real.mk_sort ctx
    | SInt -> Arithmetic.Integer.mk_sort ctx
    | _ -> failwith "unknown sort"

  let of_nullary_con ctx = function
    | Real r -> Arithmetic.Real.mk_numeral_s ctx (Q.to_string r)
    | Int n -> Arithmetic.Integer.mk_numeral_s ctx (Z.to_string n)
    | True -> Boolean.mk_true ctx
    | False -> Boolean.mk_false ctx
    | _ -> failwith "the symbol is not nullary"

  let of_con ctx args = function
    | Leq | RLeq -> (
        match args with
        | [ exp1; exp2 ] -> Arithmetic.mk_le ctx exp1 exp2
        | _ -> assert false)
    | Geq | RGeq -> (
        match args with
        | [ exp1; exp2 ] -> Arithmetic.mk_ge ctx exp1 exp2
        | _ -> assert false)
    | Lt | RLt -> (
        match args with
        | [ exp1; exp2 ] -> Arithmetic.mk_lt ctx exp1 exp2
        | _ -> assert false)
    | Gt | RGt -> (
        match args with
        | [ exp1; exp2 ] -> Arithmetic.mk_gt ctx exp1 exp2
        | _ -> assert false)
    | PDiv -> (
        match args with
        | [ exp1; exp2 ] ->
            Boolean.mk_eq ctx
              (Arithmetic.Integer.mk_mod ctx exp2 exp1)
              (Arithmetic.Integer.mk_numeral_i ctx 0)
        | _ -> assert false)
    | IsInt -> (
        match args with
        | exp :: [] -> Arithmetic.Real.mk_is_integer ctx exp
        | _ -> assert false)
    | sym ->
        if Map.Poly.mem Logic.BoolTerm.sym_sort_map sym then
          BoolTerm.of_con ctx args sym
        else if Map.Poly.mem Logic.IRBTerm.sym_sort_map sym then
          IRBTerm.of_con ctx args sym
        else failwith (Logic.ExtTerm.str_of_sym sym)

  let nullary_con_of expr =
    match BoolTerm.nullary_con_of expr with
    | Some x -> Some x
    | None -> IRBTerm.nullary_con_of expr

  let con_of mk_op_app expr =
    let term =
      if Arithmetic.is_le expr then mk_op_app (mk_leq ()) expr
      else if Arithmetic.is_ge expr then mk_op_app (mk_geq ()) expr
      else if Arithmetic.is_lt expr then mk_op_app (mk_lt ()) expr
      else if Arithmetic.is_gt expr then mk_op_app (mk_gt ()) expr
      else if Arithmetic.is_real_is_int expr then mk_op_app (mk_isint ()) expr
        (* convert to Term ignoring mismatch of sort of ite/eq
           The type will be checked after an ast is build *)
      else
        match BoolTerm.con_of mk_op_app expr with
        | Some x -> x
        | None -> (
            match IRBTerm.con_of mk_op_app expr with
            | Some x -> x
            | _ -> assert false)
    in
    Option.some term
end

module Make (Term : TermType) : sig
  val of_term : context -> sort_env_list -> Logic.term -> Z3.Expr.expr
  val term_of : sort_env_list -> Z3.Expr.expr -> Logic.term

  val check_sat :
    Logic.term list ->
    sort_env_list ->
    context ->
    (Ident.tvar * Logic.term option) list option
end = struct
  open Logic.Term

  let rec sym_of t =
    if is_con t then
      let sym, _ = let_con t in
      sym
    else if is_tyapp t then
      let t, _, _ = let_tyapp t in
      sym_of t
    else assert false

  let rec of_term ctx env term =
    if is_var term then
      let var, _ = let_var term in
      match List.findi env ~f:(fun _ (key, _) -> Stdlib.(key = var)) with
      | Some (_i, (_, sort)) ->
          Expr.mk_const ctx (of_var ctx var) (Term.of_sort ctx sort)
      | None ->
          failwith
          @@ sprintf "var %s cannot be found in the env"
               (match var with Ident.Tvar v -> v)
    else if is_con term then
      let sym, _ = let_con term in
      Term.of_nullary_con ctx sym
    else if is_app term then of_term_app ctx env term []
    else if is_bin term then
      failwith "bin to z3 expression is not implemented yet"
    else if is_let term then
      failwith "let to z3 expression is not implemented yet"
    else if is_tyapp term then
      (* actually the sort of function doesn't matter for z3 *)
      let term, _s, _ = let_tyapp term in
      of_term ctx env term
    else failwith "unknown case of term"

  and of_term_app ctx env term args =
    let t1, t2, _ = let_app term in
    let args = of_term ctx env t2 :: args in
    if is_app t1 then of_term_app ctx env t1 args
    else if is_con t1 then
      let sym, _ = let_con t1 in
      Term.of_con ctx args sym
    else if is_tyapp t1 then
      let t, _, _ = let_tyapp t1 in
      Term.of_con ctx args (sym_of t)
    else failwith "parse for App is not supported yet except for Con"

  let rec term_of senv expr =
    if Expr.ast_of_expr expr |> AST.is_var then
      let var = Expr.to_string expr in
      let index = List.length senv - Scanf.sscanf var "(:var %d)" Fn.id - 1 in
      let var, _sort = List.nth_exn senv index in
      let _ = mk_var var in
      failwith
        "the sort of the variable must be managed with something like hashtable"
    else
      match Term.nullary_con_of expr with
      | Some e -> e
      | None -> op_of_expr senv expr

  and op_of_expr senv expr =
    let mk_op_app op expr =
      match Expr.get_args expr with
      | _ :: _ as lst ->
          List.fold
            ~f:(fun acc exp -> Logic.Term.mk_app acc (term_of senv exp))
            ~init:op lst
      | _ -> assert false
    in
    match Term.con_of mk_op_app expr with Some x -> x | None -> assert false

  let map_of_model model =
    let decls = Model.get_decls model in
    List.map decls ~f:(fun decl ->
        let tvar = Ident.Tvar (Symbol.get_string (FuncDecl.get_name decl)) in
        match Model.get_const_interp model decl with
        | Some expr ->
            let t = term_of [] expr in
            (tvar, Some t)
        | None -> (tvar, None))

  let check_sat terms senv ctx =
    let solver = Solver.mk_solver ctx None in
    List.map ~f:(of_term ctx senv) terms |> Solver.add solver;
    match Solver.check solver [] with
    | SATISFIABLE ->
        let open Option.Monad_infix in
        Solver.get_model solver >>= fun model -> Some (map_of_model model)
    | _ -> None
end
