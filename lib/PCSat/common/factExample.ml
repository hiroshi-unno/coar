(* A fact clause as an example.

   A clause is [phi \/ ps \/ not ns].  When [ns] is empty and [ps] holds exactly
   one atom [P(t)], the clause says [not phi => P(t)] for every value of its
   variables: it is a positive example already, parametric in all of them and
   guarded by its premise, and it asserts exactly what the constraint does --
   no more, since it is the constraint, and no less.  A counterexample's model
   is one point of it, chosen by a solver.

   Contract: [of_clause exi_senv cl] is [Some ex] only when [cl] has no
   predicate in its premise and one in its head, and the premise is not
   identically false; [ex] is a unit positive clause whose atom applies the
   head's predicate to the head's own arguments, whose guard is the negated
   pure part, and whose parameters are every free variable of the guard and
   the arguments that is not an unknown of [exi_senv]. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

let of_clause exi_senv ((_, ps, ns, _) as cl : Clause.t) : ExClause.t option =
  if not (Set.is_empty ns && Set.length ps = 1) then None
  else
    try
      let _, pos, _, phi = Clause.to_old_clause exi_senv cl in
      match Set.to_list pos with
      | [ atom ] ->
          let cond = Evaluator.simplify @@ Formula.mk_neg phi in
          if Formula.is_false cond then None
          else
            Some (ExClause.mk_unit_pos @@ ExAtom.of_old_atom exi_senv cond atom)
      | _ -> None
    with exn_ when not (Common.Timer.is_async exn_) -> None
