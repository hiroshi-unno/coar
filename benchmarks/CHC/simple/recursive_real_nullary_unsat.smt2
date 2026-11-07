(set-logic HORN)
(define-fun-rec c () Real (+ c 1.0))
(assert true)
(check-sat)
