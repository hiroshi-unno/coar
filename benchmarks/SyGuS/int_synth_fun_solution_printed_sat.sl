; An Int-valued synth-fun: its solution must be printed as an Int define-fun.
; f(a, b) = a - b.
(set-logic LIA)
(synth-fun f ((a Int) (b Int)) Int)
(declare-var x Int)
(declare-var y Int)
(constraint (= (f x y) (- x y)))
(check-synth)
