(set-logic HORN)
(define-fun-rec f ((x Int)) Bool (ite (= (/ 1.0 0.0) 1.0) (not (f x)) true))
(assert true)
(check-sat)
