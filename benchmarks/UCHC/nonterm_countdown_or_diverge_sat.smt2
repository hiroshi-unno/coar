; Non-termination as a universally quantified CHC, on the program
;   (x := *; while (x > 0) x--)  []  diverge
; The demonic choice at l0 can take the divergent branch, so the program is non-terminating and
; the system is SATISFIABLE in every model: the least solution of Tdiv (a self-loop with no exit)
; is empty, so T0, which needs both branches to terminate, is never derived.
; Solution: Tdiv := false, T0 := false, T1 := true, Texit := true.  It is the satisfiable twin of
; nonterm_countdown_all_terminate_unsat.smt2 and, unlike it, not theory-sensitive.  expected: sat
(set-logic HORN)
(declare-fun T0 () Bool)
(declare-fun T1 (Int) Bool)
(declare-fun Texit (Int) Bool)
(declare-fun Tdiv () Bool)
(assert (forall ((x Int)) (Texit x)))
(assert (forall ((x Int))
  (=> (and (forall ((y Int)) (=> (and (> x 0) (= y (- x 1))) (T1 y)))
           (=> (<= x 0) (Texit x)))
      (T1 x))))
; diverge: a self-loop, every run from it is infinite
(assert (=> Tdiv Tdiv))
; l0: the demonic choice between the countdown (x := *) and diverge
(assert (=> (and (forall ((y Int)) (T1 y)) Tdiv) T0))
(assert (=> T0 false))
(check-sat)
