(set-logic HORN)
(define-fun-rec g ((n Int)) Int (ite (<= n 0) (div (+ n 1) 0) (g (- n 1))))
(declare-fun p (Int) Bool)
(assert (forall ((n Int)) (p n)))
; at n = 0, g 0 = div 1 0, the same term as div (2 - 1) 0 in every background
(assert (forall ((n Int)) (=> (and (p n) (= n 0)) (= (g n) (div (- 2 1) 0)))))
(check-sat)
