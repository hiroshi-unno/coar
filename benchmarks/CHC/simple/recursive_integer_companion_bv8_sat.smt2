; Expected complete defining-context satisfiability: sat.
(set-logic HORN)
(define-funs-rec ((f ((x Int)) Int) (g ((y (_ BitVec 8))) (_ BitVec 8))) ((f 0) y))
(assert true)
(check-sat)
