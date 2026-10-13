(set-logic ALL)
(define-fun-rec b ((x Bool)) Bool (b x))
(assert true)
(check-sat)
