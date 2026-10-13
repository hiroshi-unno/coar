; Expected satisfiability of the complete defining-equation context: unsat.
(set-logic HORN)
(declare-fun p () Int)
(define-fun-rec f ((x Int)) Int (+ (f x) p))
(assert (= p 1))
(check-sat)
