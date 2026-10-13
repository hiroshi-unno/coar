; unsat witness regression: parametric examples with side conditions; the checker must
; re-derive each guarded example and keep its side condition
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 3)) (P x y))))
(assert (forall ((x Int) (y Int)) (=> (and (= x 1) (= y 4)) (P x y))))
(assert (forall ((x Int) (y Int)) (=> (and (= x 2) (= y 5)) (P x y))))
(assert (forall ((x Int) (y Int)) (=> (and (= x 3) (= y 6)) (P x y))))
(assert (forall ((x Int) (y Int)) (=> (and (P x y) (= x 0)) false)))
(assert (forall ((x Int) (y Int)) (=> (and (P x y) (= x 1)) false)))
(assert (forall ((x Int) (y Int)) (=> (and (P x y) (= x 2)) false)))
(assert (forall ((x Int) (y Int)) (=> (and (P x y) (= x 3) (> y 100)) false)))
(check-sat)
