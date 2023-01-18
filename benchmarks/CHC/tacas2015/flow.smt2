(set-logic HORN)
(declare-fun P1 (Int Int Int) Bool)
(declare-fun P8 (Int Int) Bool)
(declare-fun P6 (Int) Bool)
(declare-fun P0 (Int Int) Bool)
(declare-fun P5 (Int Int) Bool)
(declare-fun P2 (Int) Bool)
(declare-fun P3 (Int) Bool)
(declare-fun P4 (Int Int) Bool)
(declare-fun P9 (Int) Bool)
(declare-fun P7 (Int Int) Bool)
(assert (forall ((x0 Int) (x1 Int)) (=> (and (P6 x0) (P6 x1)) (P7 x0 x1))))
(assert (forall ((x1 Int) (x0 Int)) (=> (P0 x0 x1) (P3 x1))))
(assert (forall ((x0 Int) (x1 Int) (x2 Int)) (=> (and (P0 x0 x1) (P5 x1 x2)) (P1 x0 x1 x2))))
(assert (forall ((x0 Int)) (=> (P3 x0) (P2 x0))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (P3 x0) (P4 x0 x1)) (P5 x0 x1))))
(assert (forall ((x0 Int)) (=> (P9 x0) (P6 x0))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (P9 x0) (P7 x0 x1)) (P8 x0 x1))))
(assert (forall ((x0 Int)) (=> true (P9 x0))))
(assert (forall ((x0 Int)) (=> (P2 x0) false)))
(check-sat)