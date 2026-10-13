; Expected full defining-context satisfiability: sat.
; Any constant integer function is a total model.
(set-logic HORN)
(define-fun-rec f ((x Int)) Int (f 0))
(assert true)
(check-sat)
