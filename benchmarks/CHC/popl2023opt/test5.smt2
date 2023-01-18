(set-logic HORN)
(declare-fun P (Bool Int) Bool)

(assert (forall ((x Bool) (k Int)) (=> (> k 0) (P x k))))
(assert (forall ((x Bool) (k Int)) (=> (P x k) (P (not x) k))))
(assert (forall ((x Bool) (k Int)) (=> (P x 0) false)))

(check-sat)