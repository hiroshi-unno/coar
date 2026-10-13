; Extension declarations (kinded predicates, relations, dependency forms) share the function
; namespace: their names must not be defined already.
(set-logic ALL)
(declare-forall-fun u () Bool)
(define-fun p () Bool true)
(declare-dep-exists-fun p (u) (Int) Bool)
(assert true)
(check-sat)
