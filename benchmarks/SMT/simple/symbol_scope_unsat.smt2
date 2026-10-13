; Declarations and definitions share one function namespace (sorts have their own).
(set-logic ALL)
(declare-fun f () Bool)
(define-fun g ((f Bool)) Bool f)
(assert (g false))
(check-sat)
