; A 4-bit y ranges over 16 values while an 8-bit c ranges over 256, so
; forall c. exists y. concat(y*y, y) = c is false.  The squared high half is
; not affine in y, so the concatenation survives the arithmetic folding and
; the equation is split into its high and low halves instead of being solved
; for y -- the shape the concatenation rule for equalities is written for.
(set-logic BV)
(assert (forall ((c (_ BitVec 8))) (exists ((y (_ BitVec 4))) (= (concat (bvmul y y) y) c))))
(check-sat)
