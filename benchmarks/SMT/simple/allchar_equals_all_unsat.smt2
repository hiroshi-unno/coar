; expected: unsat
;
; The two languages are different, so asserting that they are equal is refuted.
; z3 answers unsat; cvc5 declines an equality between regular expressions and is
; not an oracle for this one, which is why its twin beside it is written with
; membership instead.
(set-logic ALL)
(assert (= re.allchar re.all))
(check-sat)
