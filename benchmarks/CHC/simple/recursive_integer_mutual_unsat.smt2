; Expected satisfiability of the complete defining-equation context: unsat.
(set-logic HORN)
(define-funs-rec ((f ((x Int)) Int) (g ((x Int)) Int)) ((+ (g x) 1) (f x)))
(assert true)
(check-sat)
