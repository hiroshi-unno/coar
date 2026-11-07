; NOT well-founded over the reals (x -> x/2 for x > 0); WF also occurs in a body whose head the
; relation itself satisfies, so eliminating WF by resolution would answer sat.  Expected: unsat;
; PCSat answers unknown/timeout, never sat.
(set-logic HORN)
(declare-wfp WF (Real Real) Bool)
(assert (forall ((x Real) (y Real)) (=> (and (> x 0.0) (= y (/ x 2.0))) (WF x y))))
(assert (forall ((x Real) (y Real)) (=> (WF x y) (> x y))))
(check-sat)
