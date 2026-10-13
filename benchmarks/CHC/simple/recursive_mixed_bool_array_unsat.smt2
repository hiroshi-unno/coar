; Expected satisfiability of the complete defining-equation context: unsat.
(set-logic HORN)
(define-funs-rec ((b ((x Bool)) Bool) (f ((y (Array Int Int))) (Array Int Int))) ((not (b x)) y))
(assert true)
(check-sat)
