; Expected complete defining-context satisfiability: unsat.
(set-logic HORN)
(define-funs-rec ((f ((x Int)) Int) (g ((y (_ BitVec 8))) (_ BitVec 8))) ((+ (f 0) 1) y))
(assert true)
(check-sat)
