(set-logic HORN)
(define-fun-rec g ((n Int)) Int (ite (<= n 0) (div 1 0) (g (- n 1))))
(declare-fun p (Int) Bool)
(assert (forall ((n Int)) (p n)))
; false in a background with div 1 0 = 0
(assert (forall ((n Int)) (=> (p n) (not (= (g n) 0)))))
(check-sat)
