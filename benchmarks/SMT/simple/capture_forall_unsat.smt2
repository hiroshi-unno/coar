; A binder (quantifier, let, lambda or formal parameter) must not capture a global that a
; definition body mentions when that body is copied into its scope.
(set-logic ALL)
(declare-const x Int)
(define-fun g () Int x)
(assert (forall ((x Int)) (= g x)))
(check-sat)
