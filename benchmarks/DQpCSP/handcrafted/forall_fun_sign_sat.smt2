; Conjectured inexpressible with universal predicates: the universal function reaches Q through a map
; with INFINITE fibres (the sign of f(0)), so the QECHC guard of forall_fun_abs_qechc_sat.smt2 -- which names
; the finitely many preimages of an element -- is unavailable.  Every solution has
; Q(f) = {0} if f(0) >= 0 and {1} otherwise.  expected: sat
(set-logic DQHORN)
(declare-forall-fun f (Int) Int)
(declare-dep-exists-fun P (f) (Int) Bool)
(declare-dep-exists-fun Q (f) (Int) Bool)
(assert (P (f 0)))
(assert (forall ((y Int)) (=> (and (P y) (>= y 0)) (Q 0))))
(assert (forall ((y Int)) (=> (and (P y) (< y 0)) (Q 1))))
(assert (forall ((z Int) (z2 Int)) (=> (and (Q z) (Q z2) (distinct z z2)) false)))
(check-sat)
