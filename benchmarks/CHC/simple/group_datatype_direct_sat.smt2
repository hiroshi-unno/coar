; The control for group_datatype_under_array_sat.smt2 beside it: the same two-member
; `declare-datatypes` group, with the selector's sort being the sibling DIRECTLY rather than an
; array of it.  This one is read and answers `sat`, which is what says the defect is about where the
; group's members are looked for in a sort expression and not about mutual recursion as such.
;
; expected: sat
(set-logic HORN)
(declare-datatypes ((P 0) (Q 0)) (
  ( (mkP (p0 Int)) )
  ( (mkQ (q0 P)) )
))
(declare-fun I (Q) Bool)
(assert (forall ((x Q)) (=> (= (p0 (q0 x)) 0) (I x))))
(assert (forall ((x Q)) (=> (I x) (>= (p0 (q0 x)) 0))))
(check-sat)
