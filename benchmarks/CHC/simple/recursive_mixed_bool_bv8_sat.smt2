; Expected satisfiability of the complete defining-equation context: sat.
(set-logic HORN)
(define-funs-rec ((b ((x Bool)) Bool) (f ((y (_ BitVec 8))) (_ BitVec 8))) ((b x) y))
(assert true)
(check-sat)
