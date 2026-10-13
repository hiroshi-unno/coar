; Expected full defining-context satisfiability: unsat.
; At x=0 the equation requires f(0)=f(0)+1.
(set-logic HORN)
(define-fun-rec f ((x Int)) Int (+ (f 0) 1))
(assert true)
(check-sat)
