; Expected complete defining-context satisfiability: sat.
(set-logic HORN)
(define-funs-rec ((f ((x Int)) Int) (g ((y Real)) Real)) ((+ (f 0) (to_int (g 0.0))) y))
(assert (= (to_int (g 0.0)) 0))
(check-sat)
