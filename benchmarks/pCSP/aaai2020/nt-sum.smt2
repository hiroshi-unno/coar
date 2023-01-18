(set-logic HORN)

(declare-fun I (Int Int) Bool)
(assert (forall ((A Int) (B Int)) (=> (and (I B A) (<= B 0)) false)))
(assert (forall ((A Int) (B Int) (C Int) (D Int)) (=> (and (I B A) (> B 0) (= C (- B 1)) (= D (+ A B))) (or (I B A) (I C D)))))
(assert (forall ((A Int) (B Int)) (=> (and (> B 0) (= A 0)) (I B A))))


(check-sat)
(exit)
