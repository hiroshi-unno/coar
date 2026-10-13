; expected: sat
;
; The direction a repair must not overshoot into: with no repetition the
; constraint is satisfiable and `f z := 0` synthesises. cvc5 agrees.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(constraint (= (f 0) 0))
(constraint (distinct 0 1))
(check-synth)
