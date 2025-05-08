open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld

(* ToDo *)
module Debug = Debug.Make ((val Debug.Config.disable))

type kind = LB | UB

type query = {
  kind : kind;
  name : Ident.tvar;
  args : Term.t list;
  bound : Term.t;
}

type t = { preds : Pred.t list; query : query }
type solution = Valid | Invalid | Unknown | Timeout

let make preds query = { preds; query }
let flip_solution = function Valid -> Invalid | Invalid -> Valid | x -> x

let term_of_query query =
  Term.mk_fvar_app query.name
    (List.map query.args ~f:(Fn.const T_real.SReal))
    T_real.SReal query.args

let formula_of_query query =
  match query.kind with
  | LB -> Formula.leq query.bound (term_of_query query)
  | UB -> Formula.leq (term_of_query query) query.bound

let str_of_solution = function
  | Valid -> "valid"
  | Invalid -> "invalid"
  | Unknown -> "unknown"
  | Timeout -> "timeout"

let str_of prob_muclp =
  sprintf "%s\ns.t.\n%s"
    (Formula.str_of @@ formula_of_query prob_muclp.query)
    (Pred.str_of_list prob_muclp.preds)

let has_only_mu prob_muclp =
  List.for_all
    ~f:(fun pred -> Stdlib.( = ) pred.kind Predicate.Mu)
    prob_muclp.preds

let has_only_nu prob_muclp =
  List.for_all
    ~f:(fun pred -> Stdlib.( = ) pred.kind Predicate.Nu)
    prob_muclp.preds

let size_of prob_muclp = List.length prob_muclp.preds

let simplify_query query =
  { query with bound = Evaluator.simplify_term query.bound }

let simplify prob_muclp =
  {
    preds = List.map ~f:Pred.simplify prob_muclp.preds;
    query = simplify_query prob_muclp.query;
  }

let formula_of_query query =
  (match query.kind with LB -> Formula.leq | UB -> Formula.geq)
    query.bound (term_of_query query)
