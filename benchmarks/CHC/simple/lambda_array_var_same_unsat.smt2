(set-logic HORN)
(declare-fun p ((Array Int Int)) Bool)
(assert (forall ((a (Array Int Int))) (p a)))
; the two arrays are one (index 7 is overwritten), so a = that array violates
; the goal in every background: unsat
(assert (forall ((a (Array Int Int))) (=> (and (p a) (= a (store (lambda ((x Int)) x) 7 0))) (not (= a (store (lambda ((x Int)) (ite (= x 7) 1 x)) 7 0))))))
(check-sat)
