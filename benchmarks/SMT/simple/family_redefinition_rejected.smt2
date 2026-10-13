; Extension declarations (kinded predicates, relations, dependency forms) share the function
; namespace: their names must not be defined already.
(set-logic ALL)
(define-fun |F_{a,b}| () Bool true)
(declare-nwfp (F (shared) (tags (a (Int)) (b (Int)))) a b |F_{a,b}| (Int Int) Bool)
(assert true)
(check-sat)
