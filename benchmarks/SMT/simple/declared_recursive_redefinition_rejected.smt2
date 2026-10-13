; Declarations and definitions share one function namespace (sorts have their own).
(set-logic ALL)
(declare-fun f () Bool)
(define-funs-rec ((f () Bool)) (false))
(assert f)
(check-sat)
