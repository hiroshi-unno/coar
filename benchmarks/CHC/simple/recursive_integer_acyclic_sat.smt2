; Expected satisfiability of the complete defining-equation context: sat.
(set-logic HORN)
(define-fun-rec f ((x Int)) Int (+ x 1))
(assert true)
(check-sat)
