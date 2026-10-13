(set-logic HORN)
(define-fun-rec __query__ ((x Bool)) Bool (not (__query__ x)))
(assert true)
(check-sat)
