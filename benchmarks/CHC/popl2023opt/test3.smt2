(set-logic HORN)
(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (=> (P x) (P (+ x 1)))))
(assert (forall ((x Int)) (=> (P 0) false)))

(check-sat)
