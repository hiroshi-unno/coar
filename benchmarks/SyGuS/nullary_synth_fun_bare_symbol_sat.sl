; A function to synthesise of no parameters is applied as a bare symbol.
; c = 3 and b = true are a solution.
(set-logic LIA)
(synth-fun c () Int)
(synth-fun b () Bool)
(declare-var x Int)
(constraint (= c 3))
(constraint (=> b (> (+ x c) x)))
(constraint b)
(check-synth)
