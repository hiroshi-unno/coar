; UFLIA is a standard SMT-LIB logic; the reader must accept its name, and an
; uninterpreted function cannot take two values at one argument.
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 1) 2))
(assert (= (f 1) 3))
(check-sat)
