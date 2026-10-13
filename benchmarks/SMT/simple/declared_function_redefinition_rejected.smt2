; Declarations and definitions share one function namespace (sorts have their own).
(set-logic ALL)
(declare-const f Bool)
(define-fun f () Bool true)
(assert (not f))
(check-sat)
