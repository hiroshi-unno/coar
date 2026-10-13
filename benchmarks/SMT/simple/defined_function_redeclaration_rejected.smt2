; Declarations and definitions share one function namespace (sorts have their own).
(set-logic ALL)
(define-fun f () Bool true)
(declare-fun f () Bool)
(assert (not f))
(check-sat)
