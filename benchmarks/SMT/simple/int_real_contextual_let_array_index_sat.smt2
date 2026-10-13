(set-logic AUFNIRA)
(declare-const arr (Array Int Int)) (assert (= (select arr 3) 7)) (assert (let ((a 3)) (and (= (select arr a) 7) (= (+ a 0.5) 3.5))))
(check-sat)
