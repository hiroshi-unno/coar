; Unsatisfiable.  A functional predicate P over the reals whose clauses are
;   P(y) => 2y = 1        P(y) => y < 0
; The only value 2y = 1 allows is 1/2, which is not negative, so no total P
; exists.  The twin of fn_real_result_half_sat.smt2: the strategy game that
; eliminates P before the CEGIS loop must still let the refuter win here.
(set-logic HORN)
(declare-fnp P (Real) Bool)
(assert (forall ((y Real)) (=> (P y) (= (* 2.0 y) 1.0))))
(assert (forall ((y Real)) (=> (P y) (< y 0.0))))
(check-sat)
