; A binder (quantifier, let, lambda or formal parameter) must not capture a global that a
; definition body mentions when that body is copied into its scope.
(set-logic ALL)
(declare-forall-fun x () Int)
(define-fun f ((x Bool)) Bool x)
(assert (f true))
(check-sat)
