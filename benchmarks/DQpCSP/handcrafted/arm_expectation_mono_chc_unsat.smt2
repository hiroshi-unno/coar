; The false negative for POPL 2024's `expectation`.  Triple: this file,
; arm_expectation_ghost_chc_sat.smt2, arm_expectation_pred_poly_sat.smt2.  The handler averages
; the two branch answers with the weight `p`; with one refinement `A(b, r)` for every call --
; no context -- the branches are described for every client at once and the average is
; unconstrained, so `p * x + (100 - p) * y` cannot be demanded.  expected: unsat
(set-logic HORN)
(declare-fun A (Bool Int) Bool)
(declare-fun Ans (Int Int) Bool)
(assert (forall ((p Int) (r1 Int) (r2 Int))
  (=> (and (A true r1) (A false r2)) (Ans p (+ (* p r1) (* (- 100 p) r2))))))
(assert (forall ((x Int)) (A true x)))     ; some client's true branch answers x
(assert (forall ((y Int)) (A false y)))    ; and its false branch y -- for every x, y
(assert (forall ((p Int) (x Int) (y Int) (z Int))
  (=> (and (Ans p z) (not (= z (+ (* p x) (* (- 100 p) y))))) false)))
(check-sat)
