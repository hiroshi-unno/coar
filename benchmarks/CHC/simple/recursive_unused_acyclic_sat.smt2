(set-logic HORN)
(define-fun-rec b ((x Bool)) Bool (not x))
(assert true)
(check-sat)
