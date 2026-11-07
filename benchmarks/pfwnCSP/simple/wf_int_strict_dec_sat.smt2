; Well-founded over Int: 0 < x' < x (ranking x).  The real twin is wf_real_strict_dec_unsat.smt2.
; Expected: sat.
(set-logic HORN)
(declare-wfp WF (Int Int) Bool)
(assert (forall ((x Int) (x1 Int)) (=> (and (> x1 0) (< x1 x)) (WF x x1))))
(check-sat)
