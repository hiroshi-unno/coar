; Expected satisfiability of the complete defining-equation context: unsat.
(set-logic HORN)
(define-fun-rec f () Int (+ f 1))
(assert true)
(check-sat)
