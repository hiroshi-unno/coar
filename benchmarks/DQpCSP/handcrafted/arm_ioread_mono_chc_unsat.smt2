; The false negative for POPL 2024's `io-read-1`.  Triple: this file, arm_ioread_ghost_chc_sat.smt2
; and arm_ioread_pred_poly_sat.smt2.
;
; `Read` pops an element and *invents* `Err` on the empty list, so the answer depends on the
; input that remains.  With one refinement `A(z)` shared by every call of the operation, `A` has
; to hold both of `Ok` (there was input) and of `Err` (there was none), and the specification
; "reading from a non-empty list answers Ok" is refuted.  `result` is a Bool (Ok = true).
; expected: unsat
(set-logic HORN)
(declare-fun A (Bool) Bool)
(assert (A true))     ; a read that finds input answers Ok
(assert (A false))    ; a read on the empty list answers the invented Err
(assert (forall ((z Bool)) (=> (and (A z) (not z)) false)))
(check-sat)
