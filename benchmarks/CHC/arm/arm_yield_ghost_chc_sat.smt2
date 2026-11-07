; POPL 2024's repair for `yield`: the constructor annotations index the contract by the yielded
; value -- `p2(z, x)`, `p3(z, x, y)` -- which in first-order form is `A(x, r)`: given that the
; leaf yielded `x`, the value it ends up holding is `r`.  Middle file of the triple.
; expected: sat
(set-logic HORN)
(declare-fun A (Int Int) Bool)
(assert (forall ((x Int)) (A x (+ x 1))))     ; `incr` resumes with x + 1
(assert (forall ((r Int)) (=> (and (A 0 r) (not (= r 1))) false)))
(check-sat)
