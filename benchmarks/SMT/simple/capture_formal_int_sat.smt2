; A binder (quantifier, let, lambda or formal parameter) must not capture a global that a
; definition body mentions when that body is copied into its scope.
(set-logic ALL)
(declare-const x Int)
(define-fun g () Int x)
(define-fun f ((x Int)) Int g)
(assert (= x 1))
(assert (= (f 0) 1))
(check-sat)
