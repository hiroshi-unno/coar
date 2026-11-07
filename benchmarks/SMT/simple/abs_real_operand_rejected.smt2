; the Reals theory declares no abs, so (abs r) on a Real is a sort error under
; the standard (z3 accepts it as an extension)
(set-logic QF_LRA)
(declare-const r Real)
(assert (= (abs r) 1.5))
(check-sat)
