; Unsatisfiable.  The twin of fn_bool_result_true_sat.smt2 with a second clause
;   P(b) => b        P(b) => not b
; No Boolean satisfies both, so no total P exists.  This was a timeout under
; both preprocessing settings for the reason the twin states.  Expected: unsat.
(set-logic HORN)
(declare-fnp P (Bool) Bool)
(assert (forall ((b Bool)) (=> (P b) b)))
(assert (forall ((b Bool)) (=> (P b) (not b))))
(check-sat)
