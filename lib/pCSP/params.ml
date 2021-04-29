open Core
open Ast
open Ast.Logic

type t = {
  senv: SortMap.t;
  wfpvs: Ident.tvar Set.Poly.t;
  fnpvs : Ident.tvar Set.Poly.t;
  fenv : (Ident.tvar * (Ident.tvar * LogicOld.Sort.t) list * LogicOld.Sort.t * LogicOld.Term.t * (LogicOld.Formula.t Set.Poly.t)) Set.Poly.t;
  dtenv : LogicOld.DTEnv.t
}

let empty = { senv = SortMap.empty; wfpvs = Set.Poly.empty; fnpvs = Set.Poly.empty; fenv = Set.Poly.empty; dtenv = Map.Poly.empty}
let make ?(wfpvs=Set.Poly.empty) ?(fnpvs=Set.Poly.empty) ?(fenv=Set.Poly.empty) ?(dtenv=Map.Poly.empty) senv =
  { senv = senv; wfpvs = wfpvs; fnpvs = fnpvs; fenv = fenv; dtenv = dtenv}