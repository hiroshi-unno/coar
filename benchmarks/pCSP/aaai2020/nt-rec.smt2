(set-logic HORN)

(declare-fun P (Int Int) Bool)
(assert (forall ((A Int) (B Int)) (=> (and (P B A) (>= B 0)) false)))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
  (=> (and (P B D) (P A C) (= A (+ E 1)) (= B (- E 1)) (>= E 0)) (or (P E C) (P E D)))
    ))
(assert (forall ((A Int) (B Int)) (=> (and (< B 0) (= B A)) (P B A))))


(check-sat)
(exit)
