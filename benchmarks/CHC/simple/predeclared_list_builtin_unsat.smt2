; Z3 predeclares a polymorphic list datatype -- (List T) with the constructors nil and insert
; and the selectors head and tail -- and a file written against Z3 uses it without declaring
; it.  SMT-LIB itself requires declaration before use, so a reader that does not predeclare it
; stops at "unknown sort: (List Int)" and cannot read the file at all.
;
; This is the "the built-in resolves" direction.  Its twin, predeclared_list_own_unsat.smt2, is the
; other one: the same problem with a List the file declares itself, under different
; constructor names, which must keep winning over the built-in.
;
; P holds of the empty list and of nothing empty, so the system is unsatisfiable -- which the
; solver can only find out if nil and insert really are the two constructors of one datatype.
(set-logic HORN)
(declare-fun P ((List Int)) Bool)
(assert (P nil))
(assert (forall ((l (List Int))) (=> (P l) (not (= l nil)))))
(check-sat)
