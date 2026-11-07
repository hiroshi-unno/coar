; [y] stands for the declared [x]; the inner typed binding of [x] must not
; capture it, so the second constraint says x = 5 for every x: infeasible.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(declare-var x Int)
(constraint (= (f x) 0))
(constraint (let ((y x)) (let ((x Int 5)) (= y 5))))
(check-synth)
