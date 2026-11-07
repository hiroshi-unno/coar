; The twin of lra_free_bool_selects_bound_sat.smt2 in which neither value of the free Boolean
; constant b works: with b true every y must exceed 1, with b false y = x falsifies y > x.
(set-logic LRA)
(declare-fun b () Bool)
(declare-fun x () Real)
(assert (forall ((y Real))
  (and (=> b (and (or (>= y x) (< y 0.5)) (> y 1.0)))
       (=> (not b) (> y x)))))
(check-sat)
