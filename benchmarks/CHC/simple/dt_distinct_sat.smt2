; Value-level disequality must be the complement of equality.  Two values built
; by different constructors are never equal and always distinct, and the shared
; comparison returned "false" for both questions -- right for equality, backwards
; for disequality -- so this answered unsat.  z3 and cvc5 both answer sat.
(set-logic HORN)
(declare-datatype D ((A) (B)))
(assert (= (ite (distinct A B) 1 2) 1))
(check-sat)
