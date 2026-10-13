; The false negative for POPL 2024's `shift`.  Triple: this file, arm_shift_ghost_chc_sat.smt2,
; arm_shift_pred_poly_sat.smt2.  `Shift` hands the continuation to the client's `f`, which
; applies it three times; with one refinement `K(s, z)` for the continuation -- no context -- it
; must describe every delimited context the handler may be used in, so `8n + 7` is not derivable.
; expected: unsat
(set-logic HORN)
(declare-fun K (Int Int) Bool)
(assert (forall ((s Int)) (K s (+ (* 2 s) 1))))     ; one context: s * 2 + 1
(assert (forall ((s Int)) (K s (+ s 5))))           ; another, sharing the same K
(assert (forall ((n Int) (z1 Int) (z2 Int) (z3 Int))
  (=> (and (K n z1) (K z1 z2) (K z2 z3) (not (= z3 (+ (* 8 n) 7)))) false)))
(check-sat)
