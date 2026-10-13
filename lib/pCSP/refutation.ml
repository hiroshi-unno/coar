open Core
open Common.Ext
open Ast

(* A refutation a constraint solver recorded when it answered [unsat]: the DAG
   of derived example clauses that led to the contradiction, over the
   (preprocessed) problem the solver worked on.  It is the typed payload of [Problem.Unsat] for solvers
   that keep evidence; a solver whose evidence is a formula (SPACER's ground
   derivation, read by MuStrat as a counter-strategy) uses [Problem.Formula]
   instead.  Node ids are local to the refutation; [premises] refer to nodes.
   The full record with sources and the checker live in PCSat ([UnsatWitness],
   [WitnessChecker]); this is the part every consumer of a [Problem.solution]
   can carry and print. *)
type node = {
  id : int;
  example : ExClause.t;  (** the derived example clause *)
  rule : string option;  (** how it was derived, when recorded *)
  subst : LogicOld.TermSubst.t option;
      (** the substitution applied to [via], when recorded *)
  via : Clause.t option;  (** the clause it was derived from, when recorded *)
  premises : int list;  (** the examples it was derived from *)
  assumed : bool;
      (** derived from a clause received over the messenger, not from the
          problem: the refutation is conditional on it *)
}

type conclusion =
  | Conflict of ExAtom.t  (** a ground atom decided both ways *)
  | Labeling  (** the labeling problem over the leaves has no solution *)
  | Propagation of ExAtom.t list  (** unit propagation derived a conflict *)
  | FalseConstraint of Logic.sort_env_map * Logic.term
  | Countermodel of LogicOld.Formula.t * LogicOld.Formula.t
      (** formula refuted by Z3, and the model *)
  | External of string

type t = {
  senv : Logic.sort_env_map;
  conclusion : conclusion;
  nodes : node list;
  roots : int list;  (** the nodes the conclusion is drawn from *)
}

let is_conditional r = List.exists r.nodes ~f:(fun n -> n.assumed)

let str_of_node senv n =
  sprintf "  (node %d %s%s%s%s%s%s)" n.id
    (ExClause.str_of n.example)
    (match n.rule with None -> "" | Some r -> sprintf " (rule %s)" r)
    (match n.subst with
    | None -> ""
    | Some sub -> sprintf " (subst %s)" (LogicOld.TermSubst.str_of sub))
    (match n.via with
    | None -> ""
    | Some c -> sprintf " (via %s)" (Clause.str_of senv c))
    (if List.is_empty n.premises then ""
     else
       sprintf " (premises %s)"
         (String.concat_map_list n.premises ~sep:" " ~f:string_of_int))
    (if n.assumed then " (assumed)" else "")

let str_of_conclusion = function
  | Conflict atm -> sprintf "(conflict %s)" (ExAtom.str_of atm)
  | Labeling -> "(labeling-unsat)"
  | Propagation atms ->
      sprintf "(propagation-conflict %s)"
        (String.concat_map_list atms ~sep:" " ~f:ExAtom.str_of)
  | FalseConstraint (senv, t) ->
      sprintf "(false-constraint %s)"
        (Logic.ExtTerm.str_of_formula senv Map.Poly.empty t)
  | Countermodel (phi, model) ->
      sprintf "(countermodel %s (model %s))"
        (LogicOld.Formula.str_of phi)
        (LogicOld.Formula.str_of model)
  | External s -> sprintf "(external \"%s\")" s

(* one S-expression, one node per line *)
let str_of r =
  sprintf "(refutation %s%s\n (roots %s)%s)"
    (str_of_conclusion r.conclusion)
    (if is_conditional r then " (conditional)" else "")
    (String.concat_map_list r.roots ~sep:" " ~f:string_of_int)
    (String.concat_map_list r.nodes ~sep:"" ~f:(fun n ->
         "\n" ^ str_of_node r.senv n))
