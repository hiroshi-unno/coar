; Separation of DQCHC from every linear (QCHC) enlargement on the same clauses
; (DQCHC is strictly more expressive).  I must contain Q, J must contain P; the goal forbids
; I x /\ J y outside Q x, P y.  An unknown that cannot see the universal it must contain has
; to be 'true' everywhere, and two such unknowns violate the goal; an unknown that sees it
; can be equal to it and the goal becomes vacuous.  Linear enlargement J:{P,Q} >= I:{P}: J := P works.  expected: sat
(set-logic DQHORN)
(declare-forall-fun P (Int) Bool)
(declare-forall-fun Q (Int) Bool)
(declare-dep-exists-fun I (P) (Int) Bool)
(declare-dep-exists-fun J (P Q) (Int) Bool)
(assert (forall ((x Int)) (=> (Q x) (I x))))
(assert (forall ((y Int)) (=> (P y) (J y))))
(assert (forall ((x Int) (y Int)) (=> (and (I x) (J y) (not (Q x)) (not (P y))) false)))
(check-sat)
