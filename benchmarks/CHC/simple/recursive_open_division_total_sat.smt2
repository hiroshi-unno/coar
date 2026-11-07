(set-logic HORN)
(define-fun-rec f ((x Int)) Int (ite (<= x 0) (div 1 0) (f (- x 1))))
(assert true)
(check-sat)
