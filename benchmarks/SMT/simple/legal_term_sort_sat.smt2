; Control for the refusal of a twice-introduced sort name: a term named like a sort, or a
; local sort parameter named like a global sort, is legal; satisfiable.
(set-logic ALL) (declare-sort S 0) (declare-const S Bool) (assert S) (check-sat)
