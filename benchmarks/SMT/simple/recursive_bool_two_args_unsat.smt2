(set-logic ALL)
(define-fun-rec b ((x Bool) (y Bool)) Bool (not (b y x)))
(assert true)
(check-sat)
