; A backslash is an ordinary character of an SMT-LIB string literal: "a\" ends at its second quotation mark.
(set-logic QF_S)
(declare-const s String)
(assert (= s "a\"))
(assert (not (= s "b")))
(check-sat)
