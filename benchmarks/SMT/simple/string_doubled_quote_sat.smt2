; expected: sat
;
; Two spellings of the one-character string holding a quotation mark: the escape
; SMT-LIB gives a string literal is a DOUBLED quotation mark, and `\u{22}` is the
; same character written as a code point. z3 and cvc5 both answer sat.
;
; It answered unsat because the reader stripped the delimiters and stopped there,
; leaving both quotes in the value -- and because the lexer ended a literal at
; the first of the two, so a string containing a quote was split into pieces.
(set-logic ALL)
(assert (= "\u{22}" """"))
(check-sat)
