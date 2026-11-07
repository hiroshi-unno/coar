; Safe: a square is never negative, and I(y) = (y >= 0) is a solution.  Spacer
; grounds the rule's body-only x as a constant of its own and answers with a
; body that keeps it free (I(y) = y - aux*aux > -1): read existentially it is
; a solution, read universally it is false for every y.  An answer `sat` must
; come with a solution that was checked.
(set-logic HORN)
(declare-fun I (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (= y (* x x)) (I y))))
(assert (forall ((y Int)) (=> (and (I y) (< y 0)) false)))
(check-sat)
