; A binder (quantifier, let, lambda or formal parameter) must not capture a global that a
; definition body mentions when that body is copied into its scope.
(set-logic ALL)
(declare-const x (Array Int Bool))
(define-fun g () (Array Int Bool) x)
(define-fun f ((x (Array Int Bool))) (Array Int Bool) g)
(assert (distinct (f ((as const (Array Int Bool)) false)) x))
(check-sat)
