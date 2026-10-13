; The control of adm_negative_prop_sat.smt2: the fact forces the answer
; position at 1, a non-negative value, and the goal forbids values above 1/2.
; The relativisation to non-negative answer values must leave this refuted.
; Expected: unsat.
(set-logic HORN)
(declare-admp P (Real) Bool)
(assert (forall ((v Real)) (=> (= v 1.0) (P v))))
(assert (forall ((v Real)) (=> (and (P v) (> v 0.5)) false)))
(check-sat)
