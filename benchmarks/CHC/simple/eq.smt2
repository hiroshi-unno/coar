(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

(assert (forall ((x_init Int) (x Int) (y Int)) (=> (and (= x x_init) (= y 0)) (inv x_init x y))))
(assert (forall ((x_init Int) (x Int) (y Int)) (=> (and (not (= x 0)) (inv x_init x y)) (inv x_init (- x 1) (+ y 1)))))
(assert (forall ((x_init Int) (x Int) (y Int)) (=> (and (inv x_init x y) (= x 0)) (= y x_init))))
(check-sat)
