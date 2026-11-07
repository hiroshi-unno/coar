; The false negative for POPL 2024's `safe-div-1`.  Triple: this file,
; arm_safediv_ghost_chc_sat.smt2 and arm_safediv_pred_poly_sat.smt2.
;
; `optionize` wraps its body: a normal return becomes `Some`, the exception `None`.  With one
; postcondition `A(z)` for the body -- no context -- `A` must serve every client, including the
; ones whose body returns normally, so `Some` remains possible and the specification of
; `safe_div n 0`, which is `None`, is refuted.  `int option` is abstracted to its `is_Some` bit.
; expected: unsat
(set-logic HORN)
(declare-fun A (Int) Bool)      ; the body's postcondition, shared by every use of optionize
(declare-fun Ans (Bool) Bool)   ; the answer's is_Some bit
(assert (forall ((v Int)) (=> (A v) (Ans true))))    ; normal return -> Some
(assert (Ans false))                                  ; the exception -> None
(assert (forall ((v Int)) (A v)))                     ; some client's body does return normally
(assert (forall ((z Bool)) (=> (and (Ans z) z) false)))  ; safe_div n 0 must answer None
(check-sat)
