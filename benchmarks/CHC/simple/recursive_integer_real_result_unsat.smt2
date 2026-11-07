(set-logic HORN)
(define-fun-rec f ((x Int)) Real (+ (f x) 1.0))
(assert true)
(check-sat)
