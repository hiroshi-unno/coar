; .5 is a symbol, not a decimal (a decimal starts with a digit), and a symbol beginning with . is
; reserved for solvers in SMT-LIB 2.6: cvc5 1.4.2 refuses declaring it (z3 5.1.0 accepts it).
(set-logic ALL)
(declare-const .5 Real)
(assert (= .5 2.0))
(check-sat)
