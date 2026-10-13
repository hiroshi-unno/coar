; NOT well-founded over the reals: 1, 1/2, 1/4, ... is an infinite descending
; chain, so no WF relation contains it and the problem has no solution; a
; template whose strict step were a bare x > y would accept r(x) = x
(set-logic HORN)
(declare-wfp WF_R (Real Real) Bool)
(assert (forall ((x Real) (y Real)) (=> (and (> x 0.0) (= y (/ x 2.0))) (WF_R x y))))
(check-sat)
