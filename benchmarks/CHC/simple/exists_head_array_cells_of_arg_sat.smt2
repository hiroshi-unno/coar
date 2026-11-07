; An existential head over an array: for every x >= 0 some a has a[0] = x and
; a[1] = x - 1, two stores of terms over the argument: sat.
(set-logic HORN)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (>= x 0) (Q x))))
(assert (forall ((x Int)) (=> (Q x) (exists ((a (Array Int Int))) (and (= (select a 0) x) (= (select a 1) (- x 1)))))))
(check-sat)
