; expected: unsat
;
; Nested arithmetic rather than a bare literal, and refuted: 7/2 is not integral,
; so asserting that it is has no model.
(set-logic ALL)
(assert (is_int (/ 7.0 2.0)))
(check-sat)
