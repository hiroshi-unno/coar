(set-logic ALL)
(define-funs-rec ((b ((x Bool)) Bool) (c ((x Bool)) Bool)) ((not (c x)) (b x)))
(assert true)
(check-sat)
