(set-logic HORN)
(define-fun-rec f ((x Int)) Int (+ (f x) (div 1 0)))
(assert true)
(check-sat)
