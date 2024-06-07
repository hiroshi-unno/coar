open Ast.LogicOld

type ptype =
  | PAssertion of PredSubst.t * PredSubst.t * PCSP.Problem.t
  | POptimization of CHCOpt.Problem.t

type solution =
  | AssertSol of string * PCSP.Problem.solution * int
  | OptimizeSol of (CHCOpt.Problem.solution * int)

type t = string * ptype

let senv_of = function
  | _, PAssertion (_, _, pcsp) -> PCSP.Problem.senv_of pcsp
  | _, POptimization (_, pcsp) -> PCSP.Problem.senv_of pcsp
