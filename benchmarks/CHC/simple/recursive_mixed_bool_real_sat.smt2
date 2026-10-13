; Expected satisfiability of the complete defining-equation context: sat.
(set-logic HORN)
(define-funs-rec ((b ((x Bool)) Bool) (f ((y Real)) Real)) ((b x) y))
(assert true)
(check-sat)
