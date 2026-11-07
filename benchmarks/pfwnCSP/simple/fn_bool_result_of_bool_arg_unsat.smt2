; Unsatisfiable.  The twin of fn_bool_result_of_bool_arg_sat.smt2 with the
; second clause strengthened:
;   P(a, r) => (r = not a)        P(a, r) => (r and a)
; At a = false the first clause forces r = true and the second fails, so no
; total P exists: forall a. exists r. body is false at a = false.  The
; refutation is taken from the validity question only because, with the
; Boolean argument expanded into both values, it is a formula of the linear
; fragment the strategy game trusts.  Expected: unsat.
(set-logic HORN)
(declare-fnp P (Bool Bool) Bool)
(assert (forall ((a Bool) (r Bool)) (=> (P a r) (= r (not a)))))
(assert (forall ((a Bool) (r Bool)) (=> (P a r) (and r a))))
(check-sat)
