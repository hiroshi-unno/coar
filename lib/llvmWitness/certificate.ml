(* The evidence for a verdict on the direct LLVM translation's problem that a
   witness is built from, as the side that decided the verdict gives it: in
   the terms of the problem as the translation built it, predicates under
   their names and formulas over their parameters under their names.

   For a YES:
   - an invariant of a greatest-fixpoint predicate (a safety cut point [S_*])
     is a formula over its parameters that holds of every state its
     predicate is applied to on a reachable path: a post-fixpoint of its
     equation, given the others' invariants, that the query implies;
   - a transition of a least-fixpoint cut point (a termination loop head
     [W_*]) is a formula over its parameters [x] (a visit) and their copies
     [prev_name x] (an earlier visit of the same loop head, on the same
     execution, with no return to the head's function's caller between):
     a transitive relation containing every such pair, and well founded.
     The composer writes it as a loop transition invariant, which a
     validator checks for exactly these two properties.
   A predicate absent from a map has nothing to say; that only weakens the
   witness.

   For a NO, the path: the applications of the predicates along one
   execution that violates the property, in the order the execution makes
   them, from the query's, each with the value of every parameter as a
   numeral (an integer or bit-vector constant) or a Boolean constant.  A
   step may be left out (one whose predicate the side's preprocessing
   removed and could not restore); that leaves fewer waypoints, each still
   true of the execution.  The violation is the end of the path: after the
   last step, the property's failure is reachable without passing another
   predicate.  [violated_in], when given, is the predicate whose body the
   failure is in: not always the last step's, since a call's return summary
   is a step that comes after the call in the path and before the caller
   goes on to fail.

   A step's [binds] are the universally bound variables of the problem that
   take their values from the start of that step to the start of the next
   one in the path (to the violation, for the last step), in execution
   order: the nondeterministic values and the values called functions
   return, under their names in the problem, each a constant as the
   arguments are.  The first step's also begin with those the query binds
   before it.  A side that cannot tell them leaves them empty, which only
   weakens the witness.

   A step's [parent], when given, is the position (from 0) of the step whose
   body made the application: of the caller's step for a call's entry or
   return summary, of the previous visit for a loop's next one.  Positions
   count the path for [Fails] and the stem followed by the cycle for
   [Cycles].  So a failure inside a helper that the program calls from
   several places is located at the call its parent step made.  [None] for
   the query's own applications and where the side cannot tell. *)

open Ast
open Ast.LogicOld

type step = {
  pred : Ident.pvar;
  args : (Ident.tvar * Term.t) list;
  binds : (Ident.tvar * Term.t) list;
  parent : int option;
}

type t =
  | Holds of {
      invariants : (Ident.pvar, Formula.t) Core.Map.Poly.t;
      transitions : (Ident.pvar, Formula.t) Core.Map.Poly.t;
    }
  | Fails of { path : step list; violated_in : Ident.pvar option }
  | Cycles of {
      stem : step list;
      cycle : step list;
      recurrent : (Ident.pvar * Formula.t) option;
    }
      (** a NO of a termination problem: an infinite execution.  [stem] then
          [cycle] are the predicates' applications in execution order, as in
          [Fails]; the execution is the stem followed by the cycle repeated
          forever, the cycle ending where its first step began (a lasso).
          The cycle's last step's [binds] run up to that return to the loop
          head.
          [cycle = []] says only that the execution passes the stem's LAST
          step's predicate (a loop head) infinitely often: its [args] are
          empty and nothing is claimed of the values.  [recurrent], when
          given, is a set of states of that loop head the execution stays in
          at every visit (not produced yet). *)

(* The name of the copy of parameter [x] that holds its value at an earlier
   visit, in a transition. *)
let prev_name x = x ^ "__prev"

(* Invariants only, the evidence of a backend that solves the safety problem
   and nothing else. *)
let of_invariants invariants = Holds { invariants; transitions = Core.Map.Poly.empty }
