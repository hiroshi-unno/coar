; QF_LIAX is not an SMT-LIB logic name (cvc5 refuses it; z3 ignores it):
; the reader refuses it with one error line naming the logic.
(set-logic QF_LIAX)
(declare-const x Int)
(assert (> x 0))
(check-sat)
