; The same defect on arrays: an index that only one of the two stores mentions
; still has a value in the other one, its default.  Reporting "false" for such an
; index said the two arrays agree exactly where one of them was written, so two
; arrays differing at index 1 were reported equal and this answered unsat.
; z3 and cvc5 both answer sat.
(set-logic HORN)
(assert (= (ite
  (distinct (store ((as const (Array Int Int)) 0) 2 3)
            (store (store ((as const (Array Int Int)) 0) 2 3) 1 2))
  1 2) 1))
(check-sat)
