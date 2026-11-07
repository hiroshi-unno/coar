; NOT well-founded over the reals: the reachable states x > 0 of x := x / 2 form an infinite
; descending chain; the invariant P must not let the WF clause become vacuous.  Expected: unsat;
; PCSat answers unknown/timeout, never sat.
(set-logic HORN)
(declare-fun P (Real) Bool)
(declare-wfp WF (Real Real) Bool)
(assert (forall ((x Real)) (=> (> x 1.0) (P x))))
(assert (forall ((x Real) (y Real)) (=> (and (P x) (> x 0.0) (= y (/ x 2.0))) (P y))))
(assert (forall ((x Real) (y Real)) (=> (and (P x) (> x 0.0) (= y (/ x 2.0))) (WF x y))))
(check-sat)
