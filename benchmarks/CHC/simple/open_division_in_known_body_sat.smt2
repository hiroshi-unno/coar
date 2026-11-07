(set-logic HORN)
(define-fun-rec g ((n Int)) Int (ite (<= n 0) (div 1 0) (g (- n 1))))
(declare-fun p (Int) Bool)
(assert (forall ((n Int)) (p n)))
; g n = div 1 0 for every n, whatever div 1 0 is: valid in every background
(assert (forall ((n Int) (m Int)) (=> (and (p n) (p m)) (= (g n) (g m)))))
(check-sat)
