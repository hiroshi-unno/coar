(set-logic ALL)
(declare-datatype Box ((box (payload Int))))
(assert (= (payload (box 3)) 3))
(check-sat)
