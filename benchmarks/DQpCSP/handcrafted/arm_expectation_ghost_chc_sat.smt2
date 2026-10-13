; POPL 2024's repair for `expectation`: the ghost parameter `(p, x, y)` reaches the handler, so
; the refinement is indexed by the client's values -- `A(x, y, b, r)`.  Middle file of the
; triple.  expected: sat
(set-logic HORN)
(declare-fun A (Int Int Bool Int) Bool)
(declare-fun Ans (Int Int Int Int) Bool)
(assert (forall ((p Int) (x Int) (y Int) (r1 Int) (r2 Int))
  (=> (and (A x y true r1) (A x y false r2)) (Ans p x y (+ (* p r1) (* (- 100 p) r2))))))
(assert (forall ((x Int) (y Int)) (A x y true x)))
(assert (forall ((x Int) (y Int)) (A x y false y)))
(assert (forall ((p Int) (x Int) (y Int) (z Int))
  (=> (and (Ans p x y z) (not (= z (+ (* p x) (* (- 100 p) y))))) false)))
(check-sat)
