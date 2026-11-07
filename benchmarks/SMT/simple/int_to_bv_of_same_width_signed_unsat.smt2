; int_to_bv 8 (sbv_to_int x) = x for every 8-bit x: the rewrite that drops the
; round trip is sound at equal widths, so the negation is unsatisfiable.
(set-logic ALL)
(declare-fun x () (_ BitVec 8))
(assert (not (= ((_ int_to_bv 8) (sbv_to_int x)) x)))
(check-sat)
