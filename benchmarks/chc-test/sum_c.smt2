(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

(assert (forall ((x0 Int) (x Int) (r Int)) (=> (and (= x x0) (= r 0)) (inv x0 x r))))
(assert (forall ((x0 Int) (x Int) (r Int)) (=> (and (not (= x 0)) (inv x0 x r)) (inv x0 (- x 1) (+ r x)))))
(assert (forall ((x0 Int) (x Int) (r Int)) (=> (and (inv x0 x r) (= x 0)) (>= r x0))))
(check-sat)
