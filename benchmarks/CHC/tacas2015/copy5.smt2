(set-logic HORN)
(declare-fun P9 (Int) Bool)
(declare-fun P0 (Int) Bool)
(declare-fun P6 (Int Int Int) Bool)
(declare-fun P5 (Int Int Int) Bool)
(declare-fun P3 (Int Int) Bool)
(declare-fun P1 (Int) Bool)
(declare-fun P2 (Int Int) Bool)
(declare-fun P4 (Int Int) Bool)
(declare-fun P12 (Int Int Int) Bool)
(declare-fun P7 (Int Int Int Int) Bool)
(declare-fun P8 (Int) Bool)
(declare-fun P10 (Int Int) Bool)
(declare-fun P11 (Int Int) Bool)
(declare-fun P13 (Int Int Int) Bool)
(assert (forall ((x0 Int) (x1 Int)) (=> (and (P9 x0) (P9 x1) (= x1 x0)) (P11 x0 x1))))
(assert (forall ((x1 Int) (x0 Int)) (=> (and (P0 x1) (= x0 (+ 1 x1))) (P2 x1 x0))))
(assert (forall ((x0 Int) (x2 Int) (x1 Int)) (=> (P6 x0 x1 x2) (P4 x0 x2))))
(assert (forall ((x3 Int) (x1 Int) (x0 Int) (x2 Int)) (=> (and (P6 x1 x0 x2) (P5 x1 x2 x3)) (P1 x3))))
(assert (forall ((x1 Int) (x0 Int) (x2 Int) (x4 Int) (x3 Int)) (=> (and (P6 x1 x0 x2) (P5 x1 x2 x3) (P3 x3 x4)) (P7 x1 x0 x2 x4))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (P8 x0) (P8 x1) (<= x0 0) (= x1 x0)) (P10 x0 x1))))
(assert (forall ((x1 Int) (x0 Int) (x2 Int)) (=> (and (P8 x1) (P12 x1 x1 x2) (<= x1 0)) (P13 x1 x0 x2))))
(assert (forall ((x2 Int) (x1 Int) (x0 Int)) (=> (and (P8 x1) (P1 x2) (>= x1 1) (= x1 (+ 1 x0))) (P0 x2))))
(assert (forall ((x2 Int) (x3 Int) (x1 Int) (x0 Int)) (=> (and (P8 x1) (P1 x2) (P2 x2 x3) (>= x1 1) (= x1 (+ 1 x0))) (P3 x2 x3))))
(assert (forall ((x1 Int) (x3 Int) (x0 Int) (x2 Int)) (=> (and (P8 x1) (P4 x2 x3) (>= x1 1) (= x1 (+ 1 x0))) (P10 x1 x3))))
(assert (forall ((x1 Int) (x3 Int) (x4 Int) (x2 Int) (x0 Int)) (=> (and (P8 x2) (P4 x1 x3) (P12 x2 x3 x4) (>= x2 1) (= x2 (+ 1 x0))) (P5 x1 x3 x4))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (P8 x1) (>= x1 1) (= x1 (+ 1 x0))) (P8 x0))))
(assert (forall ((x0 Int) (x1 Int) (x4 Int) (x2 Int) (x3 Int)) (=> (and (P8 x2) (P10 x3 x4) (>= x2 1) (= x2 (+ 1 x3))) (P6 x0 x1 x4))))
(assert (forall ((x1 Int) (x4 Int) (x5 Int) (x0 Int) (x2 Int) (x3 Int)) (=> (and (P8 x0) (P10 x1 x4) (P7 x2 x3 x4 x5) (>= x0 1) (= x0 (+ 1 x1))) (P12 x1 x4 x5))))
(assert (forall ((x1 Int) (x0 Int) (x4 Int) (x2 Int) (x3 Int)) (=> (and (P8 x1) (P13 x2 x3 x4) (>= x1 1) (= x1 (+ 1 x2))) (P13 x1 x0 x4))))
(assert (forall ((x0 Int)) (=> true (P8 x0))))
(assert (forall ((x1 Int) (x0 Int)) (=> (P10 x0 x1) (P9 x1))))
(assert (forall ((x0 Int) (x1 Int) (x2 Int)) (=> (and (P10 x0 x1) (P11 x1 x2)) (P12 x0 x1 x2))))
(assert (forall ((x2 Int) (x0 Int) (x1 Int)) (=> (and (P13 x0 x1 x2) (or (< x2 x0) (> x2 x0))) false)))
(check-sat)
