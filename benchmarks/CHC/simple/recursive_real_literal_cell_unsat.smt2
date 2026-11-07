(set-logic HORN)
(define-fun-rec r ((x Real)) Real (+ (r 2.5) 1.0))
(assert true)
(check-sat)
