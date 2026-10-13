; The collapse of DQ to Q over a finite carrier, Q side: fin_dep_incomparable_unsat.smt2 with
; every dependency set emptied and the truth table of the dependency passed as extra arguments
; -- over a finite carrier an interpretation of a universal predicate IS a tuple of values, so
; the dependency structure becomes ordinary arguments and the prefix becomes the trivial
; exists-forall one.  The verdict must be the same as the DQ version, which is what makes the
; DQ/Q distinction collapse over finite theories (over infinite ones the distinction is strict).
; expected: unsat
(set-logic DQHORN)
(declare-forall-fun P (Bool) Bool)
(declare-forall-fun Q (Bool) Bool)
(declare-dep-exists-fun I () (Bool Bool Bool) Bool)
(declare-dep-exists-fun J () (Bool Bool Bool) Bool)
(assert (forall ((x Bool)) (=> (Q x) (I (P false) (P true) x))))
(assert (forall ((y Bool)) (=> (P y) (J (Q false) (Q true) y))))
(assert (forall ((x Bool) (y Bool))
  (=> (and (I (P false) (P true) x) (J (Q false) (Q true) y) (not (Q x)) (not (P y))) false)))
(check-sat)
