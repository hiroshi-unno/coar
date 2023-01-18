(* simple parser of fixpoint logic for debug *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld
open Parsexp
module Sexp = Ppx_sexp_conv_lib.Sexp

type logic_type = Any | Lia | BV | Reals | Arrays

let sort_of_sexp = function
  | Sexp.Atom "Int"  -> T_int.SInt
  | Sexp.Atom "Bool" -> T_bool.SBool
  | Sexp.Atom "Real" -> T_real.SReal
  | _ -> failwith "unimplemented SortExpr"

let sorts_of_sexp sexps = List.map ~f:sort_of_sexp sexps

(* Assume that every input is integer *)
let rec formula_of_sexp tenv =
  let open LogicOld in
  function
  | (Sexp.List [Sexp.Atom ">="; left; right]) ->
    let left, right = term_of_sexp tenv left, term_of_sexp tenv right in
    Formula.mk_atom (T_int.mk_geq left right)
  | (Sexp.List [Sexp.Atom "<="; left; right]) ->
    let left, right = term_of_sexp tenv left, term_of_sexp tenv right in
    Formula.mk_atom (T_int.mk_leq left right)
  | (Sexp.List [Sexp.Atom "<"; left; right]) ->
    let left, right = term_of_sexp tenv left, term_of_sexp tenv right in
    Formula.mk_atom (T_int.mk_lt left right)
  | (Sexp.List [Sexp.Atom ">"; left; right]) ->
    let left, right = term_of_sexp tenv left, term_of_sexp tenv right in
    Formula.mk_atom (T_int.mk_gt left right)
  | (Sexp.List [Sexp.Atom "="; left; right]) ->
    let left, right = term_of_sexp tenv left, term_of_sexp tenv right in
    Formula.mk_atom (T_bool.mk_eq left right)
  | (Sexp.List [Sexp.Atom "and"; left; right]) ->
    Formula.mk_and
      (formula_of_sexp tenv left)
      (formula_of_sexp tenv right)
  | (Sexp.List ((Sexp.Atom "and")::args)) -> (* for SyGuS '18 *)
    Formula.and_of (List.map ~f:(formula_of_sexp tenv) args)
  | (Sexp.List [Sexp.Atom "or";  left; right]) ->
    Formula.mk_or
      (formula_of_sexp tenv left)
      (formula_of_sexp tenv right)
  | (Sexp.List (Sexp.Atom "or"::args)) -> (* for SyGuS '18 *)
    Formula.or_of (List.map ~f:(formula_of_sexp tenv) args)
  | (Sexp.List [Sexp.Atom "=>"; left; right]) -> (* for SyGuS '18 *)
    Formula.mk_imply
      (formula_of_sexp tenv left)
      (formula_of_sexp tenv right)
  | (Sexp.List [Sexp.Atom "not"; sexp]) ->
    Formula.mk_neg (formula_of_sexp tenv sexp)
  | (Sexp.List [Sexp.Atom "ite"; cond; left; right]) -> (* for SyGuS '18 *)
    let cond' = formula_of_sexp tenv cond in
    Formula.mk_or
      (Formula.mk_and cond' (formula_of_sexp tenv left))
      (Formula.mk_and (Formula.mk_neg cond') (formula_of_sexp tenv right))
  | sexp -> failwith @@ "parse error: " ^ (Sexp.to_string_hum sexp)
and term_of_sexp tenv =
  function
  | Sexp.List [Sexp.Atom "+"; left; right] ->
    T_int.mk_add (term_of_sexp tenv left) (term_of_sexp tenv right)
  | Sexp.List (Sexp.Atom "+"::terms) -> (* for SyGuS '18 *)
    T_int.mk_sum (T_int.zero ()) (List.map ~f:(term_of_sexp tenv) terms)
  | Sexp.List [Sexp.Atom "-"; left; right] ->
    T_int.mk_sub (term_of_sexp tenv left) (term_of_sexp tenv right)
  | Sexp.List [Sexp.Atom "*"; left; right] ->
    T_int.mk_mult (term_of_sexp tenv left) (term_of_sexp tenv right)
  | Sexp.List [Sexp.Atom "/"; left; right] ->
    T_int.mk_div (term_of_sexp tenv left) (term_of_sexp tenv right)
  | Sexp.List [Sexp.Atom "ite"; cond; left; right] -> (* for SyGuS '18 *)
    T_bool.mk_if_then_else (term_of_sexp tenv cond)
      (term_of_sexp tenv left) (term_of_sexp tenv right)
  | Sexp.Atom ident -> begin
      try T_int.mk_int (Z.of_string ident)
      with _ ->
        begin
          let sort = List.Assoc.find_exn ~equal:Stdlib.(=) tenv (Ident.Tvar ident) in
          Term.mk_var (Ident.Tvar ident) sort
        end
    end
  | sexp -> failwith @@ "In term_of_sexp, fail with: " ^ (Sexp.to_string_hum sexp)
let mk_pred name sorts = (Ident.Pvar name, sorts_of_sexp sorts)
let arg_of_exp =function
  | (Sexp.List [Sexp.Atom ident; sort]) -> (Ident.Tvar ident, sort_of_sexp sort)
  | sexp -> failwith @@ "parse error (in arg_of_exp): " ^ (Sexp.to_string_hum sexp)
let args_of_exp args =
  List.map ~f:(arg_of_exp) args

let logic_type_of_str = function
  | "LIA" -> Lia | "BV" -> BV | "Reals" -> Reals | "Arrays" -> Arrays | _ -> Any

(*
let lookup' key ls =
  List.find_exn ls ~f:(fun (key', _) -> key=key')
  |> fun (_, value) -> value
*)

let mk_map tenv =
  let xs, xs' = List.unzip tenv in
  List.map2_exn xs xs' ~f:(fun (idx, _) (idx', sx') -> (idx, Term.mk_var idx' sx'))
  |> Map.Poly.of_alist_exn

let mk_inv_constraint acc tenv
    (fenv: (string, Formula.t) List.Assoc.t)
    (penv: (string, Atom.t) List.Assoc.t) cs =
  match cs with
  | [Sexp.Atom invf; Sexp.Atom pref; Sexp.Atom transf; Sexp.Atom postf] ->
    let map = mk_map tenv in
    let inv  = Formula.mk_atom (List.Assoc.find_exn ~equal:Stdlib.(=) penv invf) in
    let inv' = Formula.subst map inv in
    let pre  = Formula.mk_imply (List.Assoc.find_exn ~equal:Stdlib.(=) fenv pref) inv in
    let post = Formula.mk_imply inv (List.Assoc.find_exn ~equal:Stdlib.(=) fenv postf) in
    let trans = Formula.mk_imply
        (Formula.mk_and inv (List.Assoc.find_exn ~equal:Stdlib.(=) fenv transf))
        inv' in
    pre::trans::post::acc
  | _ -> failwith @@ "parse error (in mk_inv_constraint): " ^ (Sexp.to_string_hum @@ Sexp.List cs)

let terms_of_sexp args = Term.of_sort_env @@ args_of_exp args

let sorts_of_sexp args =
  args_of_exp args |> List.map ~f:(fun (_, sort) -> sort)

let mk_fun args def =
  let tenv = args_of_exp args in formula_of_sexp tenv def

let rec toplevel acc logic_type tenv
    (fenv: (string*Formula.t) list)
    (penv: (string*Atom.t) list) = function
  | [] -> Result.fail @@ Error.of_string "lack of check-synth command"
  | (Sexp.List [Sexp.Atom "check-synth"]) :: _ -> Ok (logic_type, acc)
  | (Sexp.List [Sexp.Atom "set-logic"; Sexp.Atom str]) :: es ->
    toplevel acc (logic_type_of_str str) tenv fenv penv es
  | (Sexp.List [Sexp.Atom "synth-inv"; Sexp.Atom name; Sexp.List args]) :: es ->
    let terms = terms_of_sexp args in
    let sorts = sorts_of_sexp args in
    let pvar  = Predicate.mk_var (Ident.Pvar name) sorts in
    let penv' = (name, Atom.mk_app pvar terms)::penv in
    toplevel acc logic_type tenv fenv penv' es
  | (Sexp.List [Sexp.Atom "declare-primed-var"; Sexp.Atom name; sort]) :: es ->
    let term  = (Ident.Tvar name, sort_of_sexp sort) in
    let term' = (Ident.Tvar (name ^ "!"), sort_of_sexp sort) in
    toplevel acc logic_type ((term,term')::tenv) fenv penv es
  | (Sexp.List [Sexp.Atom "define-fun"; Sexp.Atom name; Sexp.List args; _; def]) :: es ->
    let fenv' = (name, mk_fun args def)::fenv in
    toplevel acc logic_type tenv fenv' penv es
  | (Sexp.List ((Sexp.Atom "inv-constraint")::cs)) :: es ->
    let acc' = (mk_inv_constraint acc tenv fenv penv cs) in
    toplevel acc' logic_type tenv fenv penv es
  | (Sexp.List ((Sexp.Atom cmd)::_)) :: _ ->
    Or_error.unimplemented @@ "Cmd " ^ cmd ^ "is unimplemented."
  | sexp ->
    Result.fail @@
    Error.of_thunk (fun () ->
        "parse error : " ^ (Sexp.to_string_hum @@ Sexp.List sexp))

let toplevel = toplevel [] Any [] [] []

let from_file filename =
  let src = In_channel.read_all filename in
  match Many.parse_string src with
  | Ok (sexps) -> toplevel sexps
  | Error err ->
    Result.fail @@
    Error.of_thunk (fun () ->
        let pos = Parse_error.position err in
        let msg = Parse_error.message err in
        Printf.sprintf "at line %d, col %d: %s" pos.line pos.col msg
      )
