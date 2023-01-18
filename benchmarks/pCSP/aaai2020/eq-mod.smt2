(set-logic HORN)

(declare-fun I (Int Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (I B C A) (<= C 0) (not (= A B))) false)))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
  (=> (and (I D E C) (= A (+ C 1)) (= B (- E 1)) (> E 0)) (or (I D B A) (I D B C)))
    ))
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (= C B) (= A 0)) (I B C A))))


(check-sat)
(exit)
