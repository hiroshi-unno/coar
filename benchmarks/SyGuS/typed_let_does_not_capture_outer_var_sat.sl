; Control: the same scoping with a constraint that holds for every x, so
; f = 0 is a solution.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(declare-var x Int)
(constraint (= (f x) 0))
(constraint (let ((y x)) (let ((x Int 5)) (= (+ y x) (+ x y)))))
(constraint (let ((y Int (+ x 1))) (> y x)))
(check-synth)
