open Core
open Common
open Common.Ext
open Ast

let verbose = false

module Debug =
  Debug.Make ((val Debug.Config.(if verbose then enable else disable)))

(** Z3 interface for PropLogic.Formula *)

(* Propositional Logic Satisfiability *)

let rec pos_exprs_of_strings ctx = function
  | [] -> []
  | s :: tl -> Z3.Boolean.mk_const_s ctx s :: pos_exprs_of_strings ctx tl

let rec neg_exprs_of_strings ctx = function
  | [] -> []
  | s :: tl ->
      (Z3.Boolean.mk_not ctx @@ Z3.Boolean.mk_const_s ctx s)
      :: neg_exprs_of_strings ctx tl

let of_clause ctx (negatives, positives) =
  Z3.Boolean.mk_or ctx
  @@ pos_exprs_of_strings ctx positives
  @ neg_exprs_of_strings ctx negatives

let rec aux_of_cnf ctx acc = function
  | c :: tl -> aux_of_cnf ctx (of_clause ctx c :: acc) tl
  | [] -> acc

let of_cnf ctx cnf = aux_of_cnf ctx [] (SAT.Problem.clauses_of cnf)

let solution_of_model model =
  let decls = Z3.Model.get_decls model in
  List.map decls ~f:(fun decl ->
      match Z3.Model.get_const_interp model decl with
      | Some expr ->
          ( Z3.Symbol.get_string @@ Z3.FuncDecl.get_name decl,
            Z3.Boolean.is_true expr )
      | _ -> ("error", true))

let solve cnf =
  let cfg = [ ("model", "true"); ("proof", "true") ] in
  let ctx = Z3.mk_context cfg in
  let solver = Z3.Solver.mk_solver ctx None in
  let _ = Z3.Solver.add solver (of_cnf ctx cnf) in
  match Z3.Solver.check solver [] with
  | Z3.Solver.SATISFIABLE ->
      let open Option.Monad_infix in
      Z3.Solver.get_model solver >>= fun model -> Some (solution_of_model model)
  | _ -> None

let opt_solve (soft : SAT.Problem.soft) hard =
  let cfg = [ ("MODEL", "true") (* ("well_sorted_check", "true"); *) ] in
  let ctx = Z3.mk_context cfg in
  let optimizer = Z3.Optimize.mk_opt ctx in
  Z3.Optimize.add optimizer (of_cnf ctx hard);
  List.iter soft ~f:(fun (expr, weight) ->
      ignore
      @@ Z3.Optimize.add_soft optimizer
           (Z3.Boolean.mk_and ctx @@ of_cnf ctx expr)
           (string_of_int weight)
           (Z3.Symbol.mk_string ctx "hoge"));
  match Z3.Optimize.check optimizer with
  | SATISFIABLE ->
      let open Option.Monad_infix in
      Z3.Optimize.get_model optimizer >>= fun model ->
      let score =
        List.fold soft ~init:0 ~f:(fun score (expr, weight) ->
            score
            +
            match
              Z3.Model.eval model
                (Z3.Boolean.mk_and ctx @@ of_cnf ctx expr)
                true
            with
            | None -> 0
            | Some e -> if Z3.Boolean.is_true e then weight else 0)
      in
      Some (score, solution_of_model @@ model)
  | _ -> None

let rec of_formula ctx = function
  | PropLogic.Formula.True _ -> Z3.Boolean.mk_true ctx
  | PropLogic.Formula.False _ -> Z3.Boolean.mk_false ctx
  | PropLogic.Formula.Atom (id, _) ->
      let symbol = id |> String.escaped |> Z3.Symbol.mk_string ctx in
      Z3.Expr.mk_const ctx symbol (Z3.Boolean.mk_sort ctx)
  (*Z3.Boolean.mk_const_s ctx id*)
  | PropLogic.Formula.UnaryOp (Neg, t, _) ->
      Z3.Boolean.mk_not ctx (of_formula ctx t)
  | PropLogic.Formula.BinaryOp (And, t1, t2, _) ->
      Z3.Boolean.mk_and ctx [ of_formula ctx t1; of_formula ctx t2 ]
  | PropLogic.Formula.BinaryOp (Or, t1, t2, _) ->
      Z3.Boolean.mk_or ctx [ of_formula ctx t1; of_formula ctx t2 ]

let formula_of expr =
  if Z3.Expr.is_const expr then
    match Z3.Expr.to_string expr with
    | "true" -> PropLogic.Formula.mk_true ()
    | "false" -> PropLogic.Formula.mk_false ()
    | _ -> assert false
  else assert false

(*val check_sat: PropLogic.Formula.t -> (PropLogic.Formula.t * PropLogic.Formula.t option) list option*)
let check_sat phi =
  (*Z3.set_global_param "sat.core.minimize" "true";
    Z3.set_global_param "smt.core.minimize" "true";*)
  let cfg =
    [
      ("MODEL", "true");
      ("well_sorted_check", "true");
      (* ("sat.core.minimize", "true");
         ("smt.core.minimize", "true") *)
      (*        ("MBQI", "false"); *)
    ]
  in
  let ctx = Z3.mk_context cfg in
  let solver = Z3.Solver.mk_solver ctx None in
  let phi = of_formula ctx phi in
  (* print_endline @@ "cheking phi:" ^ (Z3.Expr.to_string phi); *)
  Z3.Solver.add solver [ phi ];
  (*debug_print_z3_input [phi];*)
  match Z3.Solver.check solver [] with
  | Z3.Solver.SATISFIABLE ->
      let open Option.Monad_infix in
      Z3.Solver.get_model solver >>= fun model ->
      (*debug_print_z3_model model;*)
      let decls = Z3.Model.get_const_decls model in
      Some
        (List.map decls ~f:(fun decl ->
             ( PropLogic.Formula.mk_atom
                 (Z3.Symbol.get_string @@ Z3.FuncDecl.get_name decl),
               Z3.Model.get_const_interp model decl >>= fun expr ->
               Some (formula_of expr) )))
  | _ -> None

(*val get_solutions: int -> PropLogic.Formula.t -> (string * bool) list list*)
let rec get_solutions up_to formula =
  if up_to <= 0 then []
  else
    match check_sat formula with
    | None -> []
    | Some model ->
        let solution =
          List.map
            ~f:(function
              | ( PropLogic.Formula.Atom (name, _),
                  Some (PropLogic.Formula.True _) ) ->
                  (name, true)
              | ( PropLogic.Formula.Atom (name, _),
                  Some (PropLogic.Formula.False _) ) ->
                  (name, false)
              | _ -> failwith "invalid model")
            model
        in
        let negation =
          PropLogic.Formula.or_of
          @@ List.map solution ~f:(fun (variable, boolean) ->
                 if boolean then
                   PropLogic.Formula.mk_neg (PropLogic.Formula.mk_atom variable)
                 else PropLogic.Formula.mk_atom variable)
        in
        let formula' = PropLogic.Formula.mk_and formula negation in
        solution :: get_solutions (up_to - 1) formula'
