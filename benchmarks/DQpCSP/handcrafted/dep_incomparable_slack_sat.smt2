; The slack example of the separation of DQCHC from QCHC: I must contain Q and may
; depend only on Q; J must contain P and may depend only on P.  Its solution set is every pair
; (I, J) of P-independent supersets of Q and Q-independent supersets of P -- 2^(2^aleph_0) many
; families -- which no linear-prefix QpCSP over the same universals can project to (cardinality
; argument).  As a solver test it is just satisfiable: I := Q, J := P.  expected: sat
(set-logic DQHORN)
(declare-forall-fun P (Int) Bool)
(declare-forall-fun Q (Int) Bool)
(declare-dep-exists-fun I (Q) (Int) Bool)
(declare-dep-exists-fun J (P) (Int) Bool)
(assert (forall ((x Int)) (=> (Q x) (I x))))
(assert (forall ((y Int)) (=> (P y) (J y))))
(check-sat)
