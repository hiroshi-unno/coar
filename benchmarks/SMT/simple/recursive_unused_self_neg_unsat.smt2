(set-logic ALL)
(define-fun-rec b ((x Bool)) Bool (not (b x)))
(assert true)
(check-sat)
