; Expected complete defining-context satisfiability: unsat.
(set-logic HORN)
(define-funs-rec ((f ((x Int)) Int) (g ((y Real)) Real)) ((+ (f 0) 1) y))
(assert true)
(check-sat)
