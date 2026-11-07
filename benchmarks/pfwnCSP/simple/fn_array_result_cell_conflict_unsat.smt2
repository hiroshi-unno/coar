; P is functional with no argument, so it holds of exactly one array, whose
; cell 0 would have to be both 5 and 6: unsat.
(set-logic HORN)
(declare-fnp P ((Array Int Int)) Bool)
(assert (forall ((a (Array Int Int))) (=> (P a) (and (= (select a 0) 5) (= (select a 0) 6)))))
(check-sat)
