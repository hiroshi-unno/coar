(set-logic HORN)

(declare-fun I (Int) Bool)
(assert (forall ((A Int)) (=> (and (I A) (< A 0)) false)))
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (I B) (= A (- B 1)) (= C (+ B 1)) (>= B 0)) (or (I A) (I C)))))
(assert (forall ((A Int)) (=> (>= A 0) (I A))))


(check-sat)
(exit)
