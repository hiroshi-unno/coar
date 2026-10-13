; Expected complete defining-context satisfiability: sat.
(set-logic HORN)
(define-funs-rec ((f ((x Int)) Int) (g ((y (Array Int Int))) (Array Int Int))) ((f 0) y))
(assert true)
(check-sat)
