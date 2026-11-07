(set-logic HORN)
(define-fun-rec r ((x Real)) Real (+ (r x) 1.0))
(assert true)
(check-sat)
