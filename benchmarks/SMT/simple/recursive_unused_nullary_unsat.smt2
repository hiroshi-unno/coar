(set-logic ALL)
(define-fun-rec b () Bool (not b))
(assert true)
(check-sat)
