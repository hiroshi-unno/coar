; Expected: sat. Boolean-valued selectors may occur directly as formulas.
(declare-datatype Flag ((flag (enabled Bool))))
(declare-const f Flag)
(assert (enabled f))
(check-sat)
