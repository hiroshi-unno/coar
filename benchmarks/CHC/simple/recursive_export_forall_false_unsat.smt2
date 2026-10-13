(set-logic HORN)
(define-fun-rec b ((x Bool)) Bool (not x))
(assert (forall ((x Bool)) (= (b x) x)))
(check-sat)
