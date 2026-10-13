(set-logic ALL)
(assert (not (> (ite true 1.5 (to_real 0)) 1.2)))
(check-sat)
