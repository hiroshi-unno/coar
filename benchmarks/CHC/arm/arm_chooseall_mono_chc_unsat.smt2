; The false negative for POPL 2024's `choose-all`.  Triple: this file,
; arm_chooseall_ghost_chc_sat.smt2, arm_chooseall_pred_poly_sat.smt2.  With one refinement
; `A(b, l)` shared by the two `Decide` calls, the inner call's answers must be described for
; every value the outer one may bind, so the concatenation is unconstrained and the
; specification `[0; x-y; y-x; 0]` cannot be demanded.  Lists are abstracted to their length.
; expected: unsat
(set-logic HORN)
(declare-fun A (Bool Int) Bool)      ; A(b, n): the branch resumed with b answers a list of length n
(declare-fun Ans (Int) Bool)
(assert (forall ((n1 Int) (n2 Int)) (=> (and (A true n1) (A false n2)) (Ans (+ n1 n2)))))
(assert (forall ((n Int)) (=> (>= n 1) (A true n))))    ; the inner call, for every context
(assert (forall ((n Int)) (=> (>= n 1) (A false n))))
(assert (forall ((n Int)) (=> (and (Ans n) (not (= n 4))) false)))
(check-sat)
