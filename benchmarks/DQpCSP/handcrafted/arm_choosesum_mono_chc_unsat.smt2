; The false negative for POPL 2024's `choose-sum`.  Triple: this file,
; arm_choosesum_ghost_chc_sat.smt2, arm_choosesum_pred_poly_sat.smt2.  One refinement `A(b, r)`
; shared by the two `Decide` calls has to describe the inner call's answers for every value the
; outer one may bind, so the sum the handler computes is unconstrained.  expected: unsat
(set-logic HORN)
(declare-fun A (Bool Int) Bool)
(declare-fun Ans (Int) Bool)
(assert (forall ((r1 Int) (r2 Int)) (=> (and (A true r1) (A false r2)) (Ans (+ r1 r2)))))
(assert (forall ((a Int) (x Int) (y Int)) (A true (- a x))))    ; the inner call, for every a
(assert (forall ((a Int) (x Int) (y Int)) (A false (- a y))))
(assert (forall ((z Int)) (=> (and (Ans z) (not (= z 0))) false)))
(check-sat)
