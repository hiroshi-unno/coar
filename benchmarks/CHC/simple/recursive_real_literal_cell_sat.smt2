(set-logic HORN)
(define-fun-rec r ((x Real)) Real (r 2.5))
(assert true)
(check-sat)
