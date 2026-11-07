; The chain's last link, x < x, is false for every x: infeasible.  A reader
; that kept only the first two operands of a chain would answer sat.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(declare-var x Int)
(constraint (= (f x) (- x 1 1)))
(constraint (< (- x 1) x (+ x 1) x))
(check-synth)
