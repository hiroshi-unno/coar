(set-logic AUFNIRA)
(assert (let ((a 3)) (and (= (+ a 0.5) 3.5) (= (div a 2) 1))))
(check-sat)
