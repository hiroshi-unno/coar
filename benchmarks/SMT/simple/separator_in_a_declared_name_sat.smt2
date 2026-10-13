; expected: sat
;
; Two different declarations, one of whose names happens to contain the string
; this process appends to a name when it hands it to the solver. The verdict is
; not what this file is for -- it is `sat` either way. What it pins is the
; MODEL: it must mention both names, with 5 for the first and 7 for the second.
;
; It printed `x |-> 5, x |-> 7`: the decoder split the solver's symbol at that
; string and kept the first piece, so the second declaration came back as the
; first and the model gave one name two values. The suffix is written after the
; name as the separator, the solving instance's id in decimal and the sort's
; short name, so it is now removed only where exactly that is found, and a name
; that merely contains the separator is kept whole.
(set-logic ALL)
(declare-const x Int)
(declare-const x__separator__y Int)
(assert (= x 5))
(assert (= x__separator__y 7))
(check-sat)
