; +2, inf and nan are ordinary symbols (z3 5.1.0 and cvc5 1.4.2 declare them): a declared +2 is
; the constant, not the number 2, so the problem is satisfiable.
(set-logic ALL)
(declare-const +2 Int)
(declare-const inf Real)
(declare-const nan Real)
(assert (and (= +2 5) (= nan inf 7.0)))
(check-sat)
