(set-logic HORN)
(declare-fun fib (Int Int) Bool)

(assert (forall ((n Int)) (=> (<= n 1) (fib n n))))
(assert (forall ((n Int) (u Int) (v Int))
           (=> (and (> n 1) (fib (- n 1) u) (fib (- n 2) v)) (fib n (+ u v)))))

(assert (forall ((m Int) (n Int))
       (=> (fib m n) (<= m (+ n 1)))))
(check-sat)
