; -p chcmax maximises the predicates the input declares, and only those.
; The existential head is skolemised into a functional predicate; that
; predicate is not an objective.  Expected: Maxsat with P(x) := x <= 10.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (and (>= x 0) (<= x 5)) (exists ((y Int)) (and (P y) (>= y x))))))
(assert (forall ((x Int)) (=> (P x) (<= x 10))))
(check-sat)
