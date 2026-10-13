; unsat witness regression: a false constraint after preprocessing; the refutation
; certificate recorded for it must be re-checked by check_solution
(set-logic HORN)
(declare-fun P (Int) Bool) (declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) (Q (+ x 1)))))
(assert (forall ((x Int)) (=> (and (Q x) (> x 0)) false)))
(check-sat)
