(set-logic AUFNIRA)
(declare-fun f (Int) Int) (assert (= (f 3) 7)) (assert (let ((a 3)) (and (= (f a) 7) (= (+ a 0.5) 3.5))))
(check-sat)
