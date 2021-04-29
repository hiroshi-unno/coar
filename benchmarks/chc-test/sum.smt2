(set-logic HORN)
(declare-fun p (Int Int) Bool)

(assert (forall ((x Int)) (=> (<= x 0) (p x 0))))
(assert (forall ((x Int) (y Int)) 
           (=> (and (> x 0) (p (- x 1) y)) (p x (+ x y)))))

(assert (forall ((x Int) (r Int))
       (=> (p x r) (>= r x))))
(check-sat)
