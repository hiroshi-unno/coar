; expected: sat
;
; The other direction, with a real literal that IS integral: `is_int 1.0` holds.
; A repair that merely stopped the crash without constraining the argument would
; still have to answer this one.
(set-logic ALL)
(assert (is_int 1.0))
(check-sat)
