; The clauses of card2_constants_sat.smt2 without the distinctness premise: a forall-sort
; ranges over every non-empty type, singletons included, so the interpretation with A = B
; is admitted, and there P A A A must hold (first clause, x = A) and must not (second
; clause, x = B = A).  expected: unsat
(set-logic DQHORN)
(declare-forall-sort a)
(declare-forall-fun A () a)
(declare-forall-fun B () a)
(declare-fun P (a a a) Bool)
(assert (forall ((x a)) (=> (= x A) (P A B x))))
(assert (forall ((x a)) (=> (and (P A B x) (= x B)) false)))
(check-sat)
