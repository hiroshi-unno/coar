; The false negative for POPL 2024's `select`.  Triple: this file, arm_select_ghost_chc_sat.smt2,
; arm_select_pred_poly_sat.smt2.  With one refinement `A(ok, h)` for every call of `Select_int`
; -- no context -- it has to hold both of a successful choice and of the invented `Failure`, so
; `Success [x]` cannot be demanded.  expected: unsat
(set-logic HORN)
(declare-fun A (Bool Int) Bool)
(assert (forall ((h Int)) (A true h)))    ; some choice succeeds, with some head
(assert (A false 0))                      ; every choice fails: the invented Failure
(assert (forall ((x Int) (ok Bool) (h Int)) (=> (and (A ok h) (not (and ok (= h x)))) false)))
(check-sat)
