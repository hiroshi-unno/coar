; expected: unsat
;
; The other direction, and the one that says the inner binding is really the one
; that answers: with the values swapped the body is false, so the assertion is
; refuted. A reader that kept the OUTER binding would answer sat here and sat on
; the twin beside it, getting one of the two right by accident.
(set-logic ALL)
(assert (let ((x true)) (let ((x false)) x)))
(check-sat)
