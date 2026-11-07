; The check is asked inside the push; the pop after it does not make the problem empty.
(set-logic QF_LIA)
(declare-const x Int)
(push 1)
(assert (and (> x 0) (< x 0)))
(check-sat)
(pop 1)
(exit)
