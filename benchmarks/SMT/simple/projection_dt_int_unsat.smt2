(set-logic ALL)
(declare-datatype Box ((box (payload Int))))
(assert (distinct (payload (box 3)) 3))
(check-sat)
