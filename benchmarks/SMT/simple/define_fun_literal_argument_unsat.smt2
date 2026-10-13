; expected: unsat
;
; The direction the repair must not overshoot into: `f 2` is 3 and not 4, so this
; is refuted. A repair that made the argument's sort fit by discarding the
; argument, or that let the call stand uninterpreted, would answer sat here.
(set-logic ALL)
(define-fun f ((n Int)) Int (+ n 1))
(assert (= (f 2) 4))
(check-sat)
