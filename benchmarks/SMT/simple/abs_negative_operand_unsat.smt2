; (abs Int Int) is declared by the SMT-LIB Ints theory: |-5| = 5, |-3| = 3, |0| = 0
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x (- 5)))
(assert (not (and (= (abs x) 5) (= (abs (- 3)) 3) (= (abs 0) 0))))
(check-sat)
