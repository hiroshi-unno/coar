(set-logic HORN)
(declare-fun P0 (Int) Bool)
(declare-fun P1 (Int Int) Bool)
(declare-fun P2 (Int Int Int) Bool)
(assert (forall ((x1 Int) (x2 Int) (x0 Int)) (=> (and (P0 x1) (P1 x1 x2) (<= x2 0) (= x0 (+ x1 x2))) (P2 x1 x2 x0))))
(assert (forall ((x1 Int) (x3 Int) (x0 Int) (x2 Int)) (=> (and (P0 x2) (P1 x2 x3) (>= x3 1) (= x3 (+ 1 x0)) (= x1 (+ 1 x2))) (P0 x1))))
(assert (forall ((x0 Int) (x1 Int) (x3 Int) (x2 Int)) (=> (and (P0 x2) (P1 x2 x3) (>= x3 1) (= x0 (+ 1 x2)) (= x3 (+ 1 x1))) (P1 x0 x1))))
(assert (forall ((x0 Int) (x1 Int) (x4 Int) (x2 Int) (x3 Int)) (=> (and (P0 x0) (P1 x0 x1) (P2 x2 x3 x4) (>= x1 1) (= x2 (+ 1 x0)) (= x1 (+ 1 x3))) (P2 x0 x1 x4))))
(assert (forall ((x0 Int)) (=> (= x0 0) (P0 x0))))
(assert (forall ((x1 Int) (x0 Int)) (=> (= x1 0) (P1 x1 x0))))
(assert (forall ((x1 Int) (x0 Int)) (=> (and (P2 0 x0 x1) (or (< x1 x0) (> x1 x0))) false)))
(check-sat)
