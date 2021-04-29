open Core
open Z3
open Common
open Common.Util
open Ast

let verbose = false
module Debug = Debug.Make (val Debug.Config.(if verbose then enable else disable))

(** Z3 interface for PropLogic.Formula *)

let rec of_formula ctx = function
  | PropLogic.Formula.True _ -> Z3.Boolean.mk_true ctx
  | PropLogic.Formula.False _ -> Z3.Boolean.mk_false ctx
  | PropLogic.Formula.Atom (id, _) ->
    let symbol = id |> String.escaped |> Symbol.mk_string ctx in
    Expr.mk_const ctx symbol (Boolean.mk_sort ctx)
  (*Z3.Boolean.mk_const_s ctx id*)
  | PropLogic.Formula.UnaryOp (Neg, t, _) -> Z3.Boolean.mk_not ctx (of_formula ctx t)
  | PropLogic.Formula.BinaryOp (And, t1, t2, _) ->
    Z3.Boolean.mk_and ctx [of_formula ctx t1; of_formula ctx t2]
  | PropLogic.Formula.BinaryOp (Or, t1, t2, _) ->
    Z3.Boolean.mk_or ctx [of_formula ctx t1; of_formula ctx t2]

let formula_of expr =
  if Expr.is_const expr then
    match Expr.to_string expr with
    | "true" -> PropLogic.Formula.mk_true ()
    | "false" -> PropLogic.Formula.mk_false ()
    | _ -> assert false
  else assert false

let model_of model =
  let open Core in
  let decls = Model.get_const_decls model in
  let open Core.Option.Monad_infix in
  List.map decls ~f:(fun decl ->
      (PropLogic.Formula.mk_atom (Symbol.get_string (FuncDecl.get_name decl)),
       Model.get_const_interp model decl >>= fun expr ->
       Some(formula_of expr)))

(* Propositional Logic Satisfiability *)
(*val check_sat: PropLogic.Formula.t -> (PropLogic.Formula.t * PropLogic.Formula.t option) list option*)
let check_sat phi =
  (*Z3.set_global_param "sat.core.minimize" "true";
    Z3.set_global_param "smt.core.minimize" "true";*)
  let cfg = [
    ("MODEL", "true");
    ("well_sorted_check", "true");
    (*        ("sat.core.minimize", "true");
              ("smt.core.minimize", "true") *)
    (*        ("MBQI", "false"); *)
  ] in
  let ctx = mk_context cfg in
  let solver = Solver.mk_solver ctx None in
  let phi = of_formula ctx phi in
  (* print_endline @@ "cheking phi:" ^ (Z3.Expr.to_string phi); *)
  Solver.add solver [phi];
  (*debug_print_z3_input [phi];*)
  match Solver.check solver [] with
  | SATISFIABLE ->
    let open Core.Option.Monad_infix in
    Solver.get_model solver >>= fun model ->
    (*debug_print_z3_model model;*)
    Some (model_of model)
      (*
      if (!CoAR.Global.config).smart_model then
        Some (smart_model_of model [phi] ctx)
      else
        Some (model_of model)
       *)
  | _ -> None

(*val solve_and_seek: int -> PropLogic.Formula.t -> (string * bool) list list*)
let rec solve_and_seek maximum formula =
  if maximum < 0 then
    failwith "maximum cannot be negative"
  else if maximum = 0 then
    []
  else
    match check_sat formula with
    | None -> []
    | Some model ->
      let solution = List.map ~f:(function
          | (PropLogic.Formula.Atom (name, _), Some (PropLogic.Formula.True _)) -> (name, true)
          | (PropLogic.Formula.Atom (name, _), Some (PropLogic.Formula.False _)) -> (name, false)
          | _ -> failwith "invalid model") model in
      let negation = PropLogic.Formula.or_of 
          (List.map ~f:(fun (variable, boolean) ->
               if boolean then PropLogic.Formula.mk_neg (PropLogic.Formula.mk_atom variable)
               else PropLogic.Formula.mk_atom variable) solution) in
      let formula' = PropLogic.Formula.mk_and formula negation in
      solution :: solve_and_seek (maximum - 1) formula'
