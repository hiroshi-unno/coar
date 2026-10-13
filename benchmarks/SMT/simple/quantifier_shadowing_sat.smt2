; expected: sat
;
; An inner binder may reuse an outer binder's name; the occurrence then refers
; to the inner one. `forall x. exists x. x` is valid -- the inner `exists` can
; pick true whatever the outer `x` is -- so the assertion is satisfiable, which
; z3 and cvc5 both report.
;
; It exited 1 with `x is already bound`: the reader inserted a binder into the
; enclosing scope with a map insertion that refuses an existing key, conflating
; two different things -- the same name twice in ONE binding list, which is
; illegal, with a nested binder shadowing an outer one, which is ordinary.
(set-logic ALL)
(assert (forall ((x Bool)) (exists ((x Bool)) x)))
(check-sat)
