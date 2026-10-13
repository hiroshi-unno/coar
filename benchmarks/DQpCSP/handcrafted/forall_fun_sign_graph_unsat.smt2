; The graph translation of forall_fun_sign_sat.smt2: at a sign-mixed R (a negative and a
; non-negative value at 0) the definite clauses force both 0 and 1 into Q and the goal fails.
; Making the goal vacuous there needs the Pi_1 guard "R has no value of the other sign", which
; quantifier-free clauses cannot express (conjectured, not proved).
; expected: unsat
(set-logic DQHORN)
(declare-forall-fun R (Int Int) Bool)
(declare-dep-exists-fun P (R) (Int) Bool)
(declare-dep-exists-fun Q (R) (Int) Bool)
(assert (forall ((y Int)) (=> (R 0 y) (P y))))
(assert (forall ((y Int)) (=> (and (P y) (>= y 0)) (Q 0))))
(assert (forall ((y Int)) (=> (and (P y) (< y 0)) (Q 1))))
(assert (forall ((z Int) (z2 Int)) (=> (and (Q z) (Q z2) (distinct z z2)) false)))
(check-sat)
