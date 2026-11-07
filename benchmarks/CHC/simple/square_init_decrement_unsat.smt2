; Unsafe: a square starts the count (y = 0 is one) and every step decrements it,
; so y = -41 is reached after 41 steps.  Interpolating the initial states
; y = x * x against y < -40 asks for a non-linear interpolant (y >= 0); an
; answer that is not one (stronger than the initial states) hides the
; counterexample.
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (= y (* x x)) (inv y))))
(assert (forall ((y Int) (z Int)) (=> (and (inv y) (= z (- y 1))) (inv z))))
(assert (forall ((y Int)) (=> (and (inv y) (< y (- 40))) false)))
(check-sat)
