; POPL 2024's repair for `safe-div-1`: the ghost parameter `(n, m)` reaches the handler, so the
; body's postcondition may be indexed by the divisor -- `A(m, v)` -- and the client with `m = 0`
; gets the empty one.  Middle file of the triple.  Plain CHC, satisfiable.  expected: sat
(set-logic HORN)
(declare-fun A (Int Int) Bool)
(declare-fun Ans (Int Bool) Bool)
(assert (forall ((m Int) (v Int)) (=> (A m v) (Ans m true))))
(assert (forall ((m Int)) (Ans m false)))
(assert (forall ((m Int) (v Int)) (=> (not (= m 0)) (A m v))))   ; m <> 0: the body returns
(assert (forall ((z Bool)) (=> (and (Ans 0 z) z) false)))        ; m = 0: the answer is None
(check-sat)
