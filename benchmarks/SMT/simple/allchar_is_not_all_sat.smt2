; expected: sat
;
; `re.allchar` is the language of the ONE-character strings and `re.all` is the
; language of every string, so the empty string is in the second and not in the
; first. Reading both symbols as `re.all` made the assertion below false in its
; first conjunct.
;
; z3 agrees; cvc5 refuses an equality between regular expressions, so the
; membership form is what both of them decide.
(set-logic ALL)
(assert (and (not (str.in.re "" re.allchar))
             (str.in.re "a" re.allchar)
             (not (str.in.re "ab" re.allchar))
             (str.in.re "" re.all)
             (str.in.re "ab" re.all)))
(check-sat)
