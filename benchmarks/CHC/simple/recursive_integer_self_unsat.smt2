; Expected satisfiability of the complete defining-equation context: unsat.
(set-logic HORN)
(define-fun-rec f ((x Int)) Int (+ (f x) 1))
(assert true)
(check-sat)
