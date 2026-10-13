; The negation of the equality case: since concat(y*y, y) cannot hit every
; 8-bit value, some y always differs from a given c, so this is true.  A
; disequality against a concatenation with a non-affine half is refuted on one
; of the two halves, whichever the model already falsifies.
(set-logic BV)
(assert (forall ((c (_ BitVec 8))) (exists ((y (_ BitVec 4))) (not (= (concat (bvmul y y) y) c)))))
(check-sat)
