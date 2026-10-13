(set-logic ALL)
(declare-datatype Box ((box (payload Real))))
(assert (distinct (payload (box 1.5)) 1.5))
(check-sat)
