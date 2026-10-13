; expected: unsat
;
; The other direction, and the one that shows the binding really is the inner
; one: with the outer `x` on the right, the constraint requires every integer to
; be zero, so the problem is infeasible and cvc5 says so. Under the old lookup
; order both sides read as the declared `x`, the constraint became `x = x`, and
; it answered sat.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(constraint (= (f 0) 0))
(declare-var x Int)
(constraint (= (let ((x 0)) x) x))
(check-synth)
