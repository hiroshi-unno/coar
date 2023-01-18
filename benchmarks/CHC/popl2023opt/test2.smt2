(set-logic HORN)
(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (=> (= 0 (mod x 2)) (P x))))
(assert (forall ((x Int)) (=> (P x) (P (+ x 2)))))
(assert (forall ((x Int)) (=> (P 1) false)))

(check-sat)
