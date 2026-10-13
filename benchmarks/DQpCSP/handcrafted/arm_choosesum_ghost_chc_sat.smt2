; POPL 2024's repair for `choose-sum`: the refinement is indexed by the call site and its ghost
; values.  Middle file of the triple.  expected: sat
(set-logic HORN)
(declare-fun A (Int Int Int Bool Int) Bool)
(declare-fun Ans (Int Int Int Int) Bool)
(assert (forall ((c Int) (p Int) (q Int) (r1 Int) (r2 Int))
  (=> (and (A c p q true r1) (A c p q false r2)) (Ans c p q (+ r1 r2)))))
(assert (forall ((x Int) (y Int)) (A 2 x y true (- (- (* 2 x) x) y))))
(assert (forall ((x Int) (y Int)) (A 2 x y false (- (- (* 2 y) x) y))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (Ans 2 x y z) (not (= z 0))) false)))
(check-sat)
