; Quoted, |-1| is a symbol (z3 5.1.0 and cvc5 1.4.2 declare it), distinct from the numeral -1.
(set-logic ALL)
(declare-fun |-1| () Int)
(assert (= |-1| 5))
(assert (< -1 0))
(check-sat)
