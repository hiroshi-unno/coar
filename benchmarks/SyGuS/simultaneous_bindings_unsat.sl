; expected: unsat
;
; The direction a repair must not overshoot into. A `let`'s bindings are
; SIMULTANEOUS, so the right-hand side `x` of `y` is the OUTER `x` and not the 0
; bound beside it; the constraint therefore requires every integer to be zero and
; the problem is infeasible, which cvc5 confirms. A repair that made the inner
; binding visible to its own siblings' right-hand sides would answer sat here.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(constraint (= (f 0) 0))
(declare-var x Int)
(constraint (= (let ((x 0) (y x)) y) 0))
(check-synth)
