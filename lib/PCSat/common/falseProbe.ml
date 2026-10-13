open Core
open Common.Ext
open Ast

(* The empty relation as a first candidate, before the template-based
   synthesizer is asked, for the rounds in which no example demands a positive
   answer.

   An example clause is the disjunction of its atoms' literals (see
   [ExClause.to_old_formula]): a negative atom [cond => P(t)] contributes
   [cond => not P(t)], which holds for every value of its parameters once [P]
   is [false]; a positive one contributes [cond => P(t)], which [false] makes
   [not cond].  So when no example clause has a predicate application among
   its positive atoms, the candidate that assigns [false] to every predicate
   satisfies every example clause that mentions a predicate at all, and a
   clause that mentions none does not depend on the candidate.  The candidate
   is then as consistent with the examples as anything the template search
   could return.

   What makes it worth proposing is the counterexample it draws.  The only
   clauses [false] can violate are those with no predicate in the premise, so
   the validator's query for such a clause mentions the clause's premise and
   nothing else, and the model leaves every position the premise does not
   constrain unassigned: the example comes back parametric there.  A
   template-based candidate that is unsatisfiable but mentions an argument
   position -- the solver returns whichever consistent assignment of the
   holes it meets first, and it has no preference for [false] -- makes the
   same query mention that position, the model assigns it, and the example
   comes back ground in it.  A fact example open at a position is what lets
   the resolution phase match it against a body atom whatever value that
   position takes; a ground one matches one value.

   Only predicates of the ordinary kind are covered: [false] violates a
   totality or existence demand ([Tot], [FN], [NE]), and the well-foundedness
   kinds carry certificates the synthesizer records alongside a candidate. *)

(* [true] when the probe may be proposed: the example set is non-empty (an
   empty one is left to the synthesizer, whose answer there is [true] and
   draws the goal clauses' negatives first), every unknown in [senv] is of the
   ordinary kind, and no example clause has a predicate application among its
   positive atoms.  A non-predicate positive atom (a pure constraint) does not
   count. *)
let applies ~(kind_map : Kind.map) ~(senv : (Ident.tvar, Logic.Sort.t) Map.Poly.t)
    (examples : ExClauseSet.t) =
  (not (Set.is_empty examples))
  && (not (Map.Poly.is_empty senv))
  && Map.Poly.for_alli senv ~f:(fun ~key ~data:_ ->
         match Map.Poly.find kind_map key with
         | Some Kind.Ord | None -> true
         | Some _ -> false)
  && Set.for_all examples ~f:(fun (cl : ExClause.t) ->
         Set.for_all cl.positive ~f:(fun atom ->
             Option.is_none (ExAtom.pvar_of atom)))

(* [false] for every unknown of [senv], as a lambda over the unknown's argument
   sorts.  The binders are named [x1], [x2], ... rather than drawn fresh, so
   that proposing the probe takes nothing from the global name counter. *)
let candidate (senv : (Ident.tvar, Logic.Sort.t) Map.Poly.t) : Logic.cand_map =
  Map.Poly.map senv ~f:(fun sort ->
      let xs =
        List.mapi (Logic.Sort.args_of sort) ~f:(fun i s ->
            (Ident.Tvar (sprintf "x%d" (i + 1)), s))
      in
      (sort, Logic.Term.mk_lambda xs (Logic.BoolTerm.mk_bool false)))
