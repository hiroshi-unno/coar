; An input that declares a datatype named unit, with two constructors of its own.  The name
; is also that of OCaml's predefined unit type, which the tool knows in every process; the
; file's declaration must win, and the predicate holding only of tt makes the query clause
; on ff hold.
(set-logic HORN)
(declare-datatypes ((unit 0)) (((tt) (ff))))
(declare-fun P (unit) Bool)
(assert (P tt))
(assert (forall ((u unit)) (=> (and (P u) (= u ff)) false)))
(check-sat)
