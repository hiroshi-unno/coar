(set-logic HORN)
(declare-fun female (Int Int) Bool)
(declare-fun male (Int Int) Bool)

(assert (forall ((m Int)) (=> (<= m 0) (female m 1))))
(assert (forall ((m Int) (n Int) (u Int)) (=> (and (> m 0) (male u (- m n)) (female (- m 1) u)) (female m n))))

(assert (forall ((m Int)) (=> (<= m 0) (male m 0))))
(assert (forall ((m Int) (n Int) (u Int)) (=> (and (> m 0) (female u (- m n)) (male (- m 1) u)) (male m n))))

(assert (forall ((n Int) (u Int) (v Int)) (=> (and (female n u) (male n v)) (<= (- u v) 1))))

(check-sat)
