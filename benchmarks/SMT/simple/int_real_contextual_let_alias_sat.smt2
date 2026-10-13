(set-logic AUFNIRA)
(assert (let ((a 3)) (let ((b a)) (and (= (div b 2) 1) (= (+ a 0.5) 3.5)))))
(check-sat)
