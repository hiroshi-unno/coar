(set-logic AUFNIRA)
(assert (= (let ((a 3)) (ite (= (div a 2) 1) (+ a 0.5) 0.0)) 3.5))
(check-sat)
