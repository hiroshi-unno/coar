(set-logic HORN)

(declare-fun I (Int Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (I B C A) (not (= A B)) (= C 0)) false)))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
  (=> (and (I D E C) (= A (+ C 1)) (= B (- E 1)) (not (= E 0))) (or (I D B A) (I D B C)))
    ))
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (= C B) (= A 0)) (I B C A))))


(check-sat)
(exit)
