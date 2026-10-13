; Twin of dep_empty_set_unsat.smt2: P is an ordinary declare-fun, so by default (an unknown
; depends on every universal declared before it) it depends on the universal predicate R declared before it,
; and P(R, x) := R x is a solution.  expected: sat
(set-logic DQHORN)
(declare-forall-fun R (Int) Bool)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (R x) (P x))))
(assert (forall ((x Int)) (=> (P x) (R x))))
(check-sat)
