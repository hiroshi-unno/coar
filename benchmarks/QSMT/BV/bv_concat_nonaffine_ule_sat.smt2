; y = 0 makes concat(y*y, y) zero, which is unsigned-below-or-equal to every
; c, so this is true.  An unsigned comparison against a concatenation with a
; non-affine half is decided high half first, low half only on a tie.
(set-logic BV)
(assert (forall ((c (_ BitVec 8))) (exists ((y (_ BitVec 4))) (bvule (concat (bvmul y y) y) c))))
(check-sat)
