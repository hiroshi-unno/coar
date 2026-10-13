(set-logic HORN)
(define-fun-rec b ((x Bool)) Bool (b x))
(assert true)
(check-sat)
