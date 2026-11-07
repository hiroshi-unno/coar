(set-logic HORN)
(define-fun-rec r ((x Real)) Real (r x))
(assert true)
(check-sat)
