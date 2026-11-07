; SMT-LIB 2.6 reserves symbols beginning with @ or . for solvers; cvc5 1.4.2 refuses declaring
; one (z3 5.1.0 accepts it).
(set-logic ALL)
(declare-const @x Int)
(assert (= @x 1))
(check-sat)
