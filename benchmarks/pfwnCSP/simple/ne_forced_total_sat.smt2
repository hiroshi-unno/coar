; Two non-empty predicates that must be disjoint, each forced by facts to hold
; at two points.  Satisfiable: P := (x = 0 \/ x = 1) and Q := (x = 2 \/ x = 3)
; satisfy every clause, and both are non-empty.
;
; What the input exercises: the non-emptiness template makes the first argument
; of a unary non-empty predicate either a constant or unconstrained, so once
; P(0), P(1) (and Q(2), Q(3)) are positive examples the only candidate left for
; each predicate is `true`.  The validator then finds the disjointness clause
; violated for every x and, x being a don't-care of the model, emits the
; parametric negative example {not P($1), not Q($1)} over one shared parameter.
; Dropping a negative atom of a non-empty predicate is sound only when the
; atom's parameters occur nowhere else in the clause -- (forall v. not P(v)) \/ R
; is refuted by non-emptiness only when v is absent from R.  Here they are
; shared, so dropping both atoms yields the empty clause and a wrong `unsat`.
; The disjunctive solution is outside the non-emptiness template, so a correct
; run of that template answers nothing (timeout or unknown); it must not answer
; `unsat`.
(set-logic HORN)
(declare-nep P (Int) Bool)
(declare-nep Q (Int) Bool)
(assert (P 0))
(assert (P 1))
(assert (Q 2))
(assert (Q 3))
(assert (forall ((x Int)) (=> (and (P x) (Q x)) false)))
(check-sat)
