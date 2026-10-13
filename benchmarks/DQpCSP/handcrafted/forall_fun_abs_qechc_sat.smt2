; The universal function of forall_fun_abs_sat.smt2
; simulated by a universal PREDICATE after all -- but only in the extended fragment (QECHC): the
; goals use NEGATED universal atoms (not (R 0 z2)) to fire only where R is single-valued at 0.
; At a graph the solution set of Q is exactly {|f(0)|}, as in the function version; at a
; non-functional R the second goal is vacuous because every element of Q comes from an R-value.
; So universal functions are separated from universal predicates in QCHC *proper*
; only; the extended condition can express the guard.  expected: sat
(set-logic DQHORN)
(declare-forall-fun R (Int Int) Bool)
(declare-dep-exists-fun P (R) (Int) Bool)
(declare-dep-exists-fun Q (R) (Int) Bool)
(assert (forall ((y Int)) (=> (R 0 y) (P y))))
(assert (forall ((y Int)) (=> (and (P y) (>= y 0)) (Q y))))
(assert (forall ((y Int)) (=> (and (P y) (< y 0)) (Q (- y)))))
(assert (forall ((z Int)) (=> (and (Q z) (< z 0)) false)))
(assert (forall ((z Int) (z2 Int))
  (=> (and (Q z) (Q z2) (distinct z z2) (not (R 0 z2)) (not (R 0 (- z2)))) false)))
(check-sat)
