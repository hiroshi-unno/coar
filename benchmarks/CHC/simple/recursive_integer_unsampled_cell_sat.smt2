(set-logic HORN)
(define-fun-rec f ((x Int)) Int (ite (= x 1) (f 1) 0))
(assert true)
(check-sat)
