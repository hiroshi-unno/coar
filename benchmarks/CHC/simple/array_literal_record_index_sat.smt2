; Satisfiable (P a := a != const false, or P a := select a (mk f0 f1) = false):
; the two array literals differ at (mk f0 f0). This tool answered unsat,0 here
; because the solver it asks answers the equality of the two literals `sat`
; when the index sort is a finite record rather than an enumeration, and the
; rewrite that avoids that question recognised only enumerations. See
; benchmarks/SMT/simple/z3_array_literal_eq_record_index_unsound.smt2.
(set-logic HORN)
(declare-datatypes ((F 0)) (((f0) (f1))))
(declare-datatypes ((M 0)) (((mk (cur F) (fin F)))))
(declare-fun P ((Array M Bool)) Bool)
(assert (P (store ((as const (Array M Bool)) true) (mk f0 f1) false)))
(assert (forall ((a (Array M Bool))) (=> (and (P a) (= a ((as const (Array M Bool)) false))) false)))
(check-sat)
