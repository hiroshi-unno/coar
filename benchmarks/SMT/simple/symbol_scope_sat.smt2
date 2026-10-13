; Declarations and definitions share one function namespace (sorts have their own).
(set-logic ALL)
(declare-sort f 0)
(define-fun f () Bool true)
(assert f)
(check-sat)
