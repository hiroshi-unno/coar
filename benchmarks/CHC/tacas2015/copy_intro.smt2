(set-logic HORN)
(declare-fun P0 (Int) Bool)
(declare-fun P1 (Int Int) Bool)
(assert (forall ((x1 Int) (x0 Int)) (=> (and (P0 x1) (= x0 0) (= x1 0)) (P1 x1 x0))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (P0 x1) (or (< x1 0) (> x1 0)) (= x1 (+ 1 x0))) (P0 x0))))
(assert (forall ((x1 Int) (x0 Int) (x2 Int) (x3 Int)) (=> (and (P0 x1) (P1 x2 x3) (or (< x1 0) (> x1 0)) (= x1 (+ 1 x2)) (= x0 (+ 1 x3))) (P1 x1 x0))))
(assert (forall ((x0 Int)) (=> true (P0 x0))))
(assert (forall ((x1 Int) (x0 Int)) (=> (P1 x0 x1) (P0 x1))))
(assert (forall ((x2 Int) (x0 Int) (x1 Int)) (=> (and (P1 x0 x1) (P1 x1 x2) (or (< x2 x0) (> x2 x0))) false)))
(check-sat)
