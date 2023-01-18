(set-logic HORN)

(declare-fun P (Int Int) Bool)
(assert (forall ((A Int) (B Int)) (=> (and (P B A) (>= B 0)) false)))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
  (=> (and (P A D) (P E C) (= A (- E 1)) (= B (+ E D)) (> E 0)) (or (P E B) (P E C)))
    ))
(assert (forall ((A Int) (B Int)) (=> (and (<= B 0) (= A 0)) (P B A))))


(check-sat)
(exit)
