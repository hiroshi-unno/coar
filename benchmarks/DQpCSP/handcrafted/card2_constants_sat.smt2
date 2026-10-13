; A cardinality assumption written by hand.  A and B are two
; universally quantified constants of the forall-sort a, and every clause assumes they
; differ (the trait law of a bound with two distinguished elements).  The unknown P takes
; them as dependent arguments -- an unknown is chosen before the universal constants, so it
; can refer to them only through its arguments -- and P(a1, a2, x) := (x = a1) is a solution:
; P A B A holds, and P A B x /\ x = B would force A = B.  Without the premise the same
; clauses are unsat (card2_constants_nopremise_unsat.smt2).  expected: sat
(set-logic DQHORN)
(declare-forall-sort a)
(declare-forall-fun A () a)
(declare-forall-fun B () a)
(declare-fun P (a a a) Bool)
(assert (forall ((x a)) (=> (and (distinct A B) (= x A)) (P A B x))))
(assert (forall ((x a)) (=> (and (distinct A B) (P A B x) (= x B)) false)))
(check-sat)
