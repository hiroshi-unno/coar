; A functional predicate is total: F(0, y) holds for some y.  Asserting that F(0, y)
; holds for no y is therefore unsatisfiable.  The plain SMT route has no place for
; the kind and must refuse this input rather than answer sat for an ordinary
; predicate; the constraint solver (-p pcsp) carries the kind.
(declare-fnp F (Int Int) Bool)
(assert (forall ((y Int)) (not (F 0 y))))
(check-sat)
