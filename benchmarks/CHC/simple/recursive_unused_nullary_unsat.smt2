(set-logic HORN)
(define-fun-rec b () Bool (not b))
(assert true)
(check-sat)
