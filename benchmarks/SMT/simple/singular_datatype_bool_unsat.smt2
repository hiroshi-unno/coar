; The singular datatype command infers its arity from the local parameters.
(set-logic ALL)
(declare-datatype E (par (T) ((box (value T)))))
(declare-const x0 (E Bool)) (declare-const x1 (E Bool)) (declare-const x2 (E Bool))
(assert (distinct x0 x1 x2))
(check-sat)
