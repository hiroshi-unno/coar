; NOT well-founded: x := x * x while x > 1 grows forever.  Expected: unsat; PCSat answers
; unknown/timeout (no cycle), never sat.
(set-logic HORN)
(declare-wfp WF (Int Int) Bool)
(assert (forall ((x Int) (x1 Int)) (=> (and (> x 1) (= x1 (* x x))) (WF x x1))))
(check-sat)
