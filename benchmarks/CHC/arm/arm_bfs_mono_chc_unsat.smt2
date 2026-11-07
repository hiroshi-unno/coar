; The false negative for POPL 2024's `bfs-simpl`.  Triple: this file, arm_bfs_ghost_chc_sat.smt2,
; arm_bfs_pred_poly_sat.smt2.  The handler queues continuations and runs them; with one
; refinement `A(ok, v)` for every queued resumption -- no context -- it must hold both of a
; success and of the exhausted-queue `Failure`, so `Success` cannot be demanded.  expected: unsat
(set-logic HORN)
(declare-fun A (Bool Int) Bool)
(assert (forall ((a Int)) (A true a)))
(assert (A false 0))
(assert (forall ((a Int) (ok Bool) (v Int))
  (=> (and (A ok v) (not (and ok (= (* v v) (* a a))))) false)))
(check-sat)
