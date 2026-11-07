; re.union and re.inter are :left-assoc in the Unicode Strings theory, so three operands are standard.
(set-logic QF_S)
(declare-const s String)
(assert (str.in_re s (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c"))))
(assert (str.in_re s (re.inter re.all (re.comp (str.to_re "a")) (re.comp (str.to_re "b")))))
(check-sat)
