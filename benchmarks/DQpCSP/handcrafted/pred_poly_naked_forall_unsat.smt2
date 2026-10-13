; Modular verification of a predicate-polymorphic definition is **strictly stronger** than the
; copying that RCaml does today, and this pair measures the difference.
;
; The definition needs its abstracted predicate to be closed under successor -- its body derives
; `P(X,a)` from `X(a)` and then relies on `X(a+1)`:
;     f : forall X. (a:{X}) -> ...        body:  X(a) ==> P(X,a),   P(X,a) ==> X(a+1)
; With `X` a *universal* symbol the second clause must hold for every X, and X := {0} refutes it,
; so the modular problem is **unsat** even though the only client instantiates at `(>= 0)`, for
; which the property does hold.  Inlining that instantiation into the definition -- one CHC copy
; per use site, which is what `Rtype.instantiate_val` does -- gives a satisfiable CHC system
; (`sat,0`; the copy is recorded in the header of pred_poly_bounded_sat.smt2).
;
; So: an encoding that substitutes the instantiation into the definition clauses is no longer a
; QCHC problem, and it answers a *weaker* question.  The fix is not to inline but to bound the
; polymorphism -- see pred_poly_bounded_sat.smt2.  expected: unsat
(set-logic DQHORN)
(declare-forall-fun X (Int) Bool)
(declare-dep-exists-fun P () ((Array Int Bool) Int) Bool)
; definition side, asserted once for every X
(assert (forall ((a Int)) (=> (X a) (P X a))))
(assert (forall ((a Int)) (=> (and (P X a) (not (X (+ a 1)))) false)))
; the only client instantiates at (>= 0)
(assert (forall ((a Int)) (=> (and (P (lambda ((b Int)) (>= b 0)) a) (< a 0)) false)))
(check-sat)
