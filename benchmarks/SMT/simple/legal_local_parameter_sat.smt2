; Control for the refusal of a twice-introduced sort name: a term named like a sort, or a
; local sort parameter named like a global sort, is legal; satisfiable.
(set-logic ALL) (define-sort T () Bool) (define-sort Id (T) T) (declare-const x (Id Int)) (assert (= x 1)) (check-sat)
