; Well-founded under its guard: x := x + y while x > 0 with y < 0 (ranking x).  Without the
; strict guard the relation stalls (wf_guarded_nonpositive_step_unsat.smt2).  Expected: sat.
(set-logic HORN)
(declare-wfp WF (Int Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int)) (=> (and (> x 0) (< y 0) (= x1 (+ x y)) (= y1 y)) (WF x y x1 y1))))
(check-sat)
