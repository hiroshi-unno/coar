; The constraint-solving entry answers one problem: with two checks, the last one, which also has
; the query P(x) => x < 0 that P(0) refutes (unsat; the first check alone is sat).  It warns on
; standard error that the earlier check is not answered.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(check-sat)
(assert (forall ((x Int)) (=> (P x) (< x 0))))
(check-sat)
