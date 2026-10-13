(set-logic AUFNIRA)
(assert (let ((a 3) (b 1)) (and (= (div a 2) 1) (= (to_int b) 1) (= (+ a b) 4.0))))
(check-sat)
