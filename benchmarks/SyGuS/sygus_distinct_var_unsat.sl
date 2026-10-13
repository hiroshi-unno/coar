; expected: unsat
;
; The same as its twin with a declared variable in place of the literal: two
; occurrences of one variable are two operands, and `distinct` is false as soon
; as two of its arguments are equal.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(declare-var x Int)
(constraint (= (f 0) 0))
(constraint (distinct x x))
(check-synth)
