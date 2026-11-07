; pop removes the assertions made since the matching push: the check sees only x > 0.
(set-logic QF_LIA)
(declare-const x Int)
(push 1)
(assert (< x 0))
(pop 1)
(assert (> x 0))
(check-sat)
(exit)
