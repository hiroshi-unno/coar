; NOT well-founded over the reals: 0 < x' < x admits 1, 1/2, 1/4, ...  The same relation over Int
; is well-founded (wf_int_strict_dec_sat.smt2).  A real ranking must decrease by a fixed amount
; (here r(x) >= r(y) + 1), not by any positive amount.  Expected: unsat; PCSat answers
; unknown/timeout (an infinite chain with no cycle is not finitely refutable), never sat.
(set-logic HORN)
(declare-wfp WF (Real Real) Bool)
(assert (forall ((x Real) (x1 Real)) (=> (and (> x1 0.0) (< x1 x)) (WF x x1))))
(check-sat)
