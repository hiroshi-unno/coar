(* The problems RCaml's constraint generator produces, each named by the
   assertion or annotation it came from.  [PAssertion (mu, nu, pcsp, lemmas)]
   is a predicate constraint satisfaction problem whose satisfiability proves
   a refinement-type assertion (or a [[@@@property]], a formula about the
   functions' graphs added as goal clauses), with the predicate variables standing for
   least ([mu]) and greatest ([nu]) fixpoints and their definitions, and the
   file's [[@@@lemma]] claims, resolved to its predicates ([lemmas], formulas
   whose free variables are universal).  The lemmas are not part of the problem:
   only MuCyc's relational proof search reads them, and it uses one only
   after proving it, so they never change which answer is right.  A
   [POptimization] is a CHC optimization problem asking for maximally precise
   refinement types. *)

open Ast.LogicOld

type ptype =
  | PAssertion of PredSubst.t * PredSubst.t * PCSP.Problem.t * Formula.t list
  | POptimization of CHCOpt.Problem.t

type solution =
  | AssertSol of string * PCSP.Problem.solution * int
  | OptimizeSol of (CHCOpt.Problem.solution * int)

type t = string * ptype

let senv_of = function
  | _, PAssertion (_, _, pcsp, _) -> PCSP.Problem.senv_of pcsp
  | _, POptimization (_, pcsp) -> PCSP.Problem.senv_of pcsp
