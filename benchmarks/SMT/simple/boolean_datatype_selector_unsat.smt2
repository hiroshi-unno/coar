; Expected: unsat. The same selector cannot be both true and false.
(declare-datatype Flag ((flag (enabled Bool))))
(declare-const f Flag)
(assert (enabled f))
(assert (not (enabled f)))
(check-sat)
