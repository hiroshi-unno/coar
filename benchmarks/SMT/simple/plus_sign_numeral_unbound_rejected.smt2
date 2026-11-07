; +2 is a symbol, not the number 2: used undeclared it is unbound, which z3 5.1.0 ("unknown
; constant") and cvc5 1.4.2 ("not declared") report as an error.
(set-logic ALL)
(declare-const x Int)
(assert (= x +2))
(check-sat)
