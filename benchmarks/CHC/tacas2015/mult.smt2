(set-logic HORN)
(declare-fun P1 (Int Int) Bool)
(declare-fun P0 (Int) Bool)
(declare-fun P2 (Int Int Int) Bool)
(assert (forall ((x3 Int) (x4 Int) (x0 Int) (x1 Int) (x2 Int)) (=> (and (P0 x3) (P1 x3 x4) (or (> x1 0) (> x2 0)) (= x0 0) (or (and (> x1 0) (<= x3 0)) (and (not (> x1 0)) (not (<= x3 0)))) (or (and (> x2 0) (<= x4 0)) (and (not (> x2 0)) (not (<= x4 0))))) (P2 x3 x4 x0))))
(assert (forall ((x2 Int) (x1 Int) (x0 Int)) (=> (and (P1 x2 x1) (P0 x2) (>= x2 1) (>= x1 1) (= x1 (+ 1 x0))) (P0 x2))))
(assert (forall ((x1 Int) (x0 Int) (x2 Int)) (=> (and (P0 x1) (P1 x1 x2) (>= x1 1) (>= x2 1) (= x2 (+ 1 x0))) (P1 x1 x0))))
(assert (forall ((x2 Int) (x1 Int) (x0 Int) (x3 Int) (x4 Int)) (=> (and (P1 x2 x1) (P0 x2) (P2 x2 x3 x4) (>= x2 1) (>= x1 1) (= x1 (+ 1 x3)) (= x0 (+ x2 x4))) (P2 x2 x1 x0))))
(assert (forall ((x0 Int)) (=> true (P0 x0))))
(assert (forall ((x1 Int) (x0 Int)) (=> (= x0 x1) (P1 x1 x0))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (P2 x0 x0 x1) (>= x0 (+ 1 x1))) false)))
(check-sat)
