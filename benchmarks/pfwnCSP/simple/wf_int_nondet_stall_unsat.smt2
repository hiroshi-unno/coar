; NOT well-founded: x' in [x - 1, x] includes the stall x' = x.  Expected: unsat.
(set-logic HORN)
(declare-wfp WF (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (> x 0) (<= y x) (>= y (- x 1))) (WF x y))))
(check-sat)
