(set-logic HORN)
(define-fun-rec f ((x Int)) Int (ite (= (div 1 0) 0) (+ (f x) 1) 0))
(assert true)
(check-sat)
