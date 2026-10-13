open Core
open Ast
open Ast.LogicOld

(* How a plain [declare-fun] or [declare-const] is read.

   SMT-LIB gives the two the same meaning -- an uninterpreted symbol that a model interprets,
   i.e. existentially quantified over interpretations.  A constraint-solving front end needs the
   other reading, where the symbol is an unknown the solver must find an interpretation for, and
   one parser serves both, so which reading applies has to travel with the environment.

   The two are not interchangeable, and in a Horn problem the difference is sharper than in SMT:
   satisfiability of a clause set asks that the clauses be *valid*, so a symbol left
   uninterpreted there is quantified universally over interpretations, which is a different
   question from the one a Horn solver answers.  That reading has its own keyword --
   [declare-forall-fun], a universally quantified function encoded as an array-sorted term
   variable -- so under the synthesis reading a plain [declare-fun] is an unknown whatever its
   result sort, and nothing is lost.

   Where the reading comes from: a [set-logic] of HORN, QHORN, DQHORN or SYGUS asks for
   synthesis and an ordinary SMT-LIB logic asks for satisfiability, but [ALL] and
   [ALL_SUPPORTED] say nothing -- a datatype benchmark and a constraint problem both declare
   them -- so for those the caller's choice stands. Hence a field rather than a function of the
   logic. *)
type decl_reading =
  | Synthesize  (** the symbol is an unknown to solve for *)
  | Uninterpreted  (** the symbol is fixed by the model, as in ordinary SMT *)

type envs = {
  decl_reading : decl_reading;
  uni_sort : Sort.t Set.Poly.t;
  uni_senv : sort_env_map;
  exi_senv : sort_env_map;
  dep_map : (Ident.tvar, sort_env_list) Map.Poly.t;
  kind_map : Ast.Kind.map;
  fenv : FunEnv.t;
  dtenv : DTEnv.t;
  candidates : (Ident.tvar, sort_env_list * Formula.t list) Map.Poly.t;
      (** candidate atoms declared per unknown by [(set-info :candidates ...)]:
          the declaration's parameters and the atoms over them, in the order
          written; hints for the hypothesis space, never asserted *)
}

type t = Formula.t
type solution = Sat of model | Unsat | Unknown

type incsol =
  | IncSat of model * (t -> incsol)
  | IncUnsat of (t -> incsol)
  | IncUnknown of (t -> incsol)

let str_of_solution = function
  | Sat model -> "sat\nmodel: " ^ str_of_model model
  | Unsat -> "unsat"
  | Unknown -> "unknown"
