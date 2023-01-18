(set-logic HORN)
(declare-fun square (Int Int) Bool)
(declare-fun sum (Int Int) Bool)

(assert (forall ((n Int)) (=> (= n 0) (square n n))))
(assert (forall ((n Int) (u Int)) (=> (and (> n 0) (square (- n 1) u)) (square n (- (+ u n n) 1)))))

(assert (forall ((n Int)) (=> (= n 0) (sum n n))))
(assert (forall ((n Int) (u Int)) (=> (and (> n 0) (sum (- n 1) u)) (sum n (+ n u)))))

(assert (forall ((n Int) (u Int) (v Int)) (=> (and (>= n 0) (sum n u) (square n v)) (= (+ u u) (+ n v)))))

(check-sat)
