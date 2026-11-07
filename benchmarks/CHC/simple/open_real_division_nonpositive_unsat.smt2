; Expected: unsat.
;
; `(/ 1.0 0.0)` is a term the theory of reals leaves open: each model fixes
; its value, and different models fix different ones.  In a model where it is
; 0 (or any non-positive number) the first clause forces P 0 and the second
; forbids it, so no interpretation of P works in that model and the system has
; no solution -- a solution must hold in every model.
;
; It answered `sat` because the constant folder evaluated the quotient with
; arbitrary-precision rationals, whose division by zero returns positive
; infinity rather than failing; `inf <= 0.0` then folded to false and the
; first clause disappeared.  The folder now leaves a real division by zero
; alone, as it does an integer one.
(set-logic HORN)
(declare-fun P (Real) Bool)
(assert (=> (<= (/ 1.0 0.0) 0.0) (P 0.0)))
(assert (=> (P 0.0) false))
(check-sat)
