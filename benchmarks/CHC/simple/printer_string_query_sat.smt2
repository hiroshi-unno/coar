; expected: sat
; Removing a generated query must not rewrite an unrelated string value.
(set-logic HORN)
(declare-fun P (String) Bool)
(assert (P "__query__"))
(assert (not (P "false")))
(check-sat)
