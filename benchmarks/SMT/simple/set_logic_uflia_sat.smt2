; UFLIA is a standard SMT-LIB logic (uninterpreted functions with linear
; integer arithmetic); the reader must accept its name.
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (> (f 0) (f 1)))
(check-sat)
