; Expected complete defining-context satisfiability: unsat.
(set-logic HORN)
(define-funs-rec ((f ((x Int)) Int) (g ((y (Array Int Int))) (Array Int Int))) ((+ (f 0) 1) y))
(assert true)
(check-sat)
