; The singular datatype command infers its arity from the local parameters.
(set-logic ALL)
(declare-datatype E (par (T U) ((pair (first T) (second U)))))
(declare-const x0 (E Bool Bool)) (declare-const x1 (E Bool Bool)) (declare-const x2 (E Bool Bool)) (declare-const x3 (E Bool Bool)) (declare-const x4 (E Bool Bool))
(assert (distinct x0 x1 x2 x3 x4))
(check-sat)
