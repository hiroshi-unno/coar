; QF_FP is a standard SMT-LIB logic name whose theory (FloatingPoint) this
; tool does not implement: the reader refuses it with one error line naming
; the logic, not with an exception.  z3 and cvc5 answer sat.
(set-logic QF_FP)
(declare-const p Bool)
(assert p)
(check-sat)
