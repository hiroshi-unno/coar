; expected: sat
; Annotation-looking text inside a string is data, not an SMT annotation.
(set-logic HORN)
(declare-fun P (String) Bool)
(assert (P "(! a"))
(assert (not (P "a")))
(check-sat)
