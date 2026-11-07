; P = {y | y > 0} is a solution
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (< x 0) (P (abs x)))))
(assert (forall ((y Int)) (=> (and (P y) (<= y 0)) false)))
(check-sat)
