; Nothing after exit is executed.
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 1))
(exit)
(assert (= x 2))
(check-sat)
