; Expected satisfiability of the complete defining-equation context: sat.
(set-logic HORN)
(declare-fun p () Int)
(define-fun-rec f ((x Int)) Int (+ (f x) p))
(assert (= p 0))
(check-sat)
