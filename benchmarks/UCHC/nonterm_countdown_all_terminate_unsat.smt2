; Non-termination as a universally quantified CHC: T_l is the set of configurations from which
; every run terminates, and the goal demands that the initial configuration is outside it.
;
; Program:  l0: x := *;  l1: while (x > 0) x--;  exit
; Every run terminates, so "every initial configuration diverges" is false and the system is
; UNSATISFIABLE over the intended structure Z.  T_l(x) is the complement of the divergent set at
; location l: the configurations from which every run terminates.  Its least solution makes T_l1
; true everywhere, so T_l0 holds and the goal fails.
;
; Why this file exists: it is theory-sensitive.  In a non-standard model Z* of Th(Z) the least
; solution of T_l1 is only the standard part (a countdown from a non-standard x never reaches exit
; in finitely many steps), so the premise (forall y. T_l1 y) fails, T_l0 is not derived and the
; system is satisfiable there.  So:  standard: unsat;  some model (SMT's "modulo T"): sat;
; every model (this repository's per-model definition): unsat.  expected: unsat
(set-logic HORN)
(declare-fun T0 () Bool)
(declare-fun T1 (Int) Bool)
(declare-fun Texit (Int) Bool)
; exit has no successors: every run from it terminates
(assert (forall ((x Int)) (Texit x)))
; l1: from x, every successor is either (x > 0, x - 1) at l1 or (x <= 0, x) at exit
(assert (forall ((x Int))
  (=> (and (forall ((y Int)) (=> (and (> x 0) (= y (- x 1))) (T1 y)))
           (=> (<= x 0) (Texit x)))
      (T1 x))))
; l0: x := * branches over every integer
(assert (=> (forall ((y Int)) (T1 y)) T0))
; the initial configuration must diverge
(assert (=> T0 false))
(check-sat)
