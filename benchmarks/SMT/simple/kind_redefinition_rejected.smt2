; Extension declarations (kinded predicates, relations, dependency forms) share the function
; namespace: their names must not be defined already.
(set-logic ALL)
(define-fun p () Bool true)
(declare-dwfp p (Int Int) Bool)
(assert true)
(check-sat)
