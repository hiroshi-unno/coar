(set-logic HORN)
(declare-fun P0 (Int Int Int) Bool)
(declare-fun P2 (Int) Bool)
(declare-fun P6 (Int Int Int) Bool)
(declare-fun P1 (Int) Bool)
(declare-fun P3 (Int Int) Bool)
(declare-fun P4 (Int Int) Bool)
(declare-fun P5 (Int Int Int) Bool)
(assert (forall ((x1 Int) (x0 Int)) (=> (and (P2 x1) (= x0 (+ 1 x1))) (P4 x1 x0))))
(assert (forall ((x1 Int) (x0 Int) (x3 Int) (x2 Int)) (=> (and (P2 x1) (P6 x1 x2 x3) (= x2 (+ 1 x1))) (P0 x1 x0 x3))))
(assert (forall ((x1 Int) (x2 Int) (x0 Int)) (=> (and (P1 x1) (P3 x1 x2) (>= x2 (+ 1 x1))) (P5 x1 x2 x0))))
(assert (forall ((x0 Int)) (=> (>= x0 0) (P1 x0))))
(assert (forall ((x0 Int)) (=> (>= x0 0) (P2 x0))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (P4 x0 x1) (>= x0 0)) (P3 x0 x1))))
(assert (forall ((x0 Int) (x1 Int) (x2 Int)) (=> (and (P4 x0 x1) (P5 x0 x1 x2) (>= x0 0)) (P6 x0 x1 x2))))
(assert (forall ((x1 Int) (x0 Int)) (=> (and (P1 x0) (P3 x0 x1) (<= x1 x0)) false)))
(check-sat)
