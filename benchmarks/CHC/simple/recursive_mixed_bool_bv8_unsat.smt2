; Expected satisfiability of the complete defining-equation context: unsat.
(set-logic HORN)
(define-funs-rec ((b ((x Bool)) Bool) (f ((y (_ BitVec 8))) (_ BitVec 8))) ((not (b x)) y))
(assert true)
(check-sat)
