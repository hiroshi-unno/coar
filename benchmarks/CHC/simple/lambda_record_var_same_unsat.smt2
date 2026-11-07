(set-logic HORN)
(declare-datatypes ((W 0)) (((mk (arr (Array Int Int))))))
(declare-fun p (W) Bool)
(assert (forall ((w W)) (p w)))
; the two records are one (index 7 is overwritten), so unsat
(assert (forall ((w W)) (=> (and (p w) (= w (mk (store (lambda ((x Int)) x) 7 0)))) (not (= w (mk (store (lambda ((x Int)) (ite (= x 7) 1 x)) 7 0)))))))
(check-sat)
