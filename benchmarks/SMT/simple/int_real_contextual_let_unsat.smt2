(set-logic AUFNIRA)
(assert (let ((a 3)) (and (= (div a 2) 1) (not (= (+ a 0.5) 3.5)))))
(check-sat)
