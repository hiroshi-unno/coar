(set-logic HORN)
(declare-fun f (Int) Bool)

(assert (forall ((x Int)) (=> (= 0 (mod x 4)) (f x))))
(assert (forall ((x Int)) (=> (f x) (f (+ x 4)))))
(assert (forall ((x Int)) (=> (and (f x) (f (+ x 1))) false)))

(check-sat)
