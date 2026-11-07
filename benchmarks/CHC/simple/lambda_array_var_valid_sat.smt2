(set-logic HORN)
(declare-fun p ((Array Int Int)) Bool)
(assert (forall ((a (Array Int Int))) (p a)))
; no a equals both arrays: they differ at index 0 (0 against 3), so sat
(assert (forall ((a (Array Int Int))) (=> (and (p a) (= a (store (lambda ((x Int)) x) 7 0))) (not (= a (store ((as const (Array Int Int)) 3) 7 0))))))
(check-sat)
