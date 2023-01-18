(set-logic HORN)
(declare-fun P (Int) Bool)

(assert (forall ((k Int)) (=> (and (> k -3) (< k 3)) (P k))))
(assert (forall ((k Int)) (=> (P k) (P (- 0 k)))))
(assert (forall ((k Int)) (=> (P 3) false)))

(check-sat)