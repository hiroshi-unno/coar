(set-logic ALL)
(define-fun-rec b ((x Bool)) Bool (let ((y (b x))) (not y)))
(assert true)
(check-sat)
