(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)
(declare-fnp fnp (Int Int) Bool)
(declare-wfp wfp (Int Int) Bool)

(assert (forall ((x0 Int) (x Int) (r Int)) (=> (and (= x x0) (= r 0)) (inv x0 x r))))
(assert (forall ((x0 Int) (x Int) (r Int)) (=> (and (> x 0) (inv x0 x r)) (inv x0 (- x 1) (+ r x)))))
(assert (forall ((x0 Int) (x Int) (r Int) (f_ret Int)) (=> (and (inv x0 x r) (<= x 0) (fnp x0 f_ret)) (>= r f_ret))))
(assert (forall ((x0 Int) (x Int) (r Int)) (=> (and (> x 0) (inv x0 x r)) (wfp x (- x 1)))))
(check-sat)
