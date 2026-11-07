; NOT well-founded: with y <= 0 allowed, y = 0 gives the self-loop (x, 0) -> (x, 0).  Expected: unsat.
(set-logic HORN)
(declare-wfp WF (Int Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int)) (=> (and (> x 0) (<= y 0) (= x1 (+ x y)) (= y1 y)) (WF x y x1 y1))))
(check-sat)
