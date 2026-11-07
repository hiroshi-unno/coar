; A well-founded relation relates no element to itself, so no well-founded P has P(0, 0):
; unsatisfiable.  The plain SMT route reads one formula and has no place for the kind,
; so it must refuse this input rather than answer for an ordinary predicate (which
; would be sat); the constraint solver (-p pcsp) carries the kind and answers unsat.
(declare-wfp P (Int Int) Bool)
(assert (P 0 0))
(check-sat)
