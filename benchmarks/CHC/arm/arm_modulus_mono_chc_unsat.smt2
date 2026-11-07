; The false negative for POPL 2024's `modulus`.  Triple: this file,
; arm_modulus_ghost_chc_sat.smt2, arm_modulus_pred_poly_sat.smt2.  `mu` probes a sequence and its
; answer is the probed value; with one contract `S(n, v)` for every sequence -- no context -- the
; contract must admit every sequence the clients may pass, so the answer at index 10 is not
; pinned and `mu f a = mu f b` cannot be concluded.  expected: unsat
(set-logic HORN)
(declare-fun S (Int Int) Bool)
(declare-fun Ans (Int) Bool)
(assert (forall ((v Int)) (=> (S 10 v) (Ans v))))
(assert (forall ((n Int) (v Int)) (S n v)))            ; one contract for all sequences
(assert (forall ((r Int) (z Int)) (=> (and (Ans z) (not (= z r))) false)))
(check-sat)
