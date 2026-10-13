(set-logic ALL)
(declare-fun P ((Seq Real)) Bool)
(assert (P (seq.unit 1.0)))
(check-sat)
