; expected: sat
;
; The same with the quote inside the string rather than alone, which is what
; needs the lexer to keep reading past it: `a"b` written both ways.
(set-logic ALL)
(assert (= "a""b" "a\u{22}b"))
(check-sat)
