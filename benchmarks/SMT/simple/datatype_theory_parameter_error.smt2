; SMT-LIB 2.7 forbids theory-sort names as datatype parameters; the input must be refused, by name.
(set-logic ALL)
(declare-datatypes ((E 1)) ((par (Int) ((box (value Int))))))
(declare-const x0 (E Bool))
(declare-const x1 (E Bool))
(declare-const x2 (E Bool))
(assert (distinct x0 x1 x2))
(check-sat)
