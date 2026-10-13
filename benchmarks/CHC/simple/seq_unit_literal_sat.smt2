(set-logic ALL)
(declare-fun P ((Seq Int)) Bool)
(assert (P (seq.unit 1)))
(check-sat)
