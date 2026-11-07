; P(0) and P(x) /\ x < 5 => P(x + 1): satisfiable, least solution 0 <= x <= 5.
; Beside it, step_from_zero_bounded_sat.above_least.candidate (define-funs, as
; a .sol file holds them) is a solution that is NOT least (0 <= x <= 6): a
; minimality check must not certify it.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (P 0))
(assert (forall ((x Int)) (=> (and (P x) (< x 5)) (P (+ x 1)))))
(check-sat)
