(set-logic HORN)
(declare-fun P0 (Int Int Int) Bool)
(declare-fun P6 (Int Int) Bool)
(declare-fun P5 (Int Int) Bool)
(declare-fun P1 (Int) Bool)
(declare-fun P2 (Int Int) Bool)
(declare-fun P3 (Int) Bool)
(declare-fun P4 (Int Int Int) Bool)
(assert (forall ((x1 Int) (x0 Int)) (=> (P6 x0 x1) (P3 x1))))
(assert (forall ((x0 Int) (x1 Int) (x2 Int)) (=> (and (P6 x0 x1) (P5 x1 x2)) (P0 x0 x1 x2))))
(assert (forall ((x1 Int) (x2 Int) (x0 Int)) (=> (and (P1 x1) (P2 x1 x2) (= x1 x2)) (P4 x1 x2 x0))))
(assert (forall ((x0 Int)) (=> true (P1 x0))))
(assert (forall ((x0 Int) (x1 Int)) (=> (P3 x1) (P2 x0 x1))))
(assert (forall ((x1 Int) (x2 Int) (x0 Int)) (=> (and (P3 x1) (P4 x0 x1 x2)) (P5 x1 x2))))
(assert (forall ((x0 Int) (x1 Int)) (=> true (P6 x0 x1))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (P1 x0) (P2 x0 x1) (or (< x0 x1) (> x0 x1))) false)))
(check-sat)
