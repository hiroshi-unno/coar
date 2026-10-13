; Expected complete defining-context satisfiability: sat.
(set-logic HORN)
(define-funs-rec ((f ((x Int)) Int) (g ((y Real)) Real)) ((f 0) y))
(assert true)
(check-sat)
