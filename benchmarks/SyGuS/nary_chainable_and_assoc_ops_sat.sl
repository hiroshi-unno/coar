; Operators applied to more than two operands, read by their SMT-LIB
; attributes: = and the orders chainable, - div xor left-associative,
; => right-associative.  f x = x - 2 satisfies every constraint; reading
; (=> false true false) left-associatively would make it false.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(declare-var x Int)
(constraint (= (f x) (- x 1 1)))
(constraint (<= (- x 3) (f x) (- x 2) x))
(constraint (= (f 2) 0 (- 2 2)))
(constraint (=> false true false))
(constraint (xor true true true))
(constraint (= (div 100 5 2) 10))
(check-synth)
