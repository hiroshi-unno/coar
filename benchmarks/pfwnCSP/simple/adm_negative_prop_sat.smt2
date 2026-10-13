; An admissible unknown whose answer position (the last argument) is forced
; at -1 by a fact and forbidden negative by a goal.  Over the reals this is
; refuted in one resolution step; the answer position ranges over the
; non-negative extended reals, where neither clause has an instance and
; P = {0} is a solution.  Expected: sat.
(set-logic HORN)
(declare-admp P (Real) Bool)
(assert (forall ((v Real)) (=> (= v (- 1.0)) (P v))))
(assert (forall ((v Real)) (=> (and (P v) (< v 0.0)) false)))
(check-sat)
