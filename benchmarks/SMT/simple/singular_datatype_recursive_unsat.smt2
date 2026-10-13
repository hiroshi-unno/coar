; The singular datatype command infers its arity from the local parameters.
(set-logic ALL)
(declare-datatype E (par (T) ((nil) (cons (head T) (tail (E T))))))
(declare-const x (E Bool))
(assert (not (head (cons true x))))
(check-sat)
