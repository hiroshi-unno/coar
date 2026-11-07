; P is functional with no argument and an array result with a[0] = 5 and
; a[1] = -3: two stores over any array are a witness, while an array template
; that is a constant array has none: sat.
(set-logic HORN)
(declare-fnp P ((Array Int Int)) Bool)
(assert (forall ((a (Array Int Int))) (=> (P a) (and (= (select a 0) 5) (= (select a 1) (- 3))))))
(check-sat)
