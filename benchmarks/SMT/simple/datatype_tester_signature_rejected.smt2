; Ill-sorted explicit tester signature: must be refused before any verdict.
(set-logic ALL)
(declare-datatype E (par (T) ((a) (b))))
(declare-const x (E Bool))
(declare-const y (E Int))
(assert ((_ is (a () (E Int))) x))
(check-sat)
