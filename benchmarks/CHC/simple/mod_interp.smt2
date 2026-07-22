(declare-rel interp (Int Int))
(declare-var A Int)
(declare-var B Int)
(rule (=> (and (>= B 0) (= (- B A) 0)) (interp B A)))
(rule (=> (interp B A) (and (=> (= A 1) (= 1 (mod B 2))) (=> (= A 2) (= 0 (mod B 2))))))

(check-sat)
(exit)