; unsat witness regression: a unit-propagation refutation through an inductive loop; the refutation
; certificate recorded for it must be re-checked by check_solution
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 10)) (Inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 5)) false)))
(check-sat)
