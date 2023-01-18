(set-logic HORN)
(declare-fun inv (Int Int) Bool)

(assert (forall ((x Int) (r Int)) (=> (and (= x 10) (= r 0)) (inv x r))))
(assert (forall ((x Int) (r Int)) (=> (and (not (= x 0)) (inv x r)) (inv (- x 1) (+ r x)))))
(assert (forall ((x Int) (r Int)) (=> (and (inv x r) (= x 0)) (>= r 10))))
(check-sat)
