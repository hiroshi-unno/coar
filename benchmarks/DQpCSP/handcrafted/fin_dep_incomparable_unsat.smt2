; The collapse of DQ to Q over a finite carrier, DQ side: the incomparable-dependency example
; (dep_incomparable_unsat.smt2) over a FINITE carrier (Bool).  I must contain Q but sees only P, J must contain P
; but sees only Q, and the goal forbids I x /\ J y outside Q x, P y.  Each unknown that cannot see
; what it must contain is forced to be true everywhere, and the goal then fails: unsat.
; Its trivial-prefix encoding fin_dep_incomparable_encoded_unsat.smt2 must agree.  expected: unsat
(set-logic DQHORN)
(declare-forall-fun P (Bool) Bool)
(declare-forall-fun Q (Bool) Bool)
(declare-dep-exists-fun I (P) (Bool) Bool)
(declare-dep-exists-fun J (Q) (Bool) Bool)
(assert (forall ((x Bool)) (=> (Q x) (I x))))
(assert (forall ((y Bool)) (=> (P y) (J y))))
(assert (forall ((x Bool) (y Bool)) (=> (and (I x) (J y) (not (Q x)) (not (P y))) false)))
(check-sat)
