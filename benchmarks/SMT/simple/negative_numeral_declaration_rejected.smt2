; -1 is a negative numeral, never a symbol: z3 5.1.0 and cvc5 1.4.2 refuse its declaration
; ("symbol expected"), so the reader refuses it too, and keeps reading the atom -1 as the number.
(set-logic ALL)
(declare-const -1 Int)
(assert (= -1 5))
(check-sat)
