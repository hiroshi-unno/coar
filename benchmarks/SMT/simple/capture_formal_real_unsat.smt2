; A binder (quantifier, let, lambda or formal parameter) must not capture a global that a
; definition body mentions when that body is copied into its scope.
(set-logic ALL)
(declare-const x Real)
(define-fun g () Real x)
(define-fun f ((x Real)) Real g)
(assert (distinct (f 0.0) x))
(check-sat)
