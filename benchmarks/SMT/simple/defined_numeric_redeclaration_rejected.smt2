; Declarations and definitions share one function namespace (sorts have their own).
(set-logic ALL)
(define-funs-rec ((f () Int)) (1))
(declare-fun f () Int)
(assert (not (= f 1)))
(check-sat)
