; Unsigned bit-vector order is bounded: x = 255 has nothing above it, so
; forall x. exists y. x <u y is false.  The counterpart of the same shape over
; the integers, where it is true -- a reminder that the integer projection's
; answer must not be reused for bit-vectors.  Exercises the comparison rule.
(set-logic BV)
(assert (forall ((x (_ BitVec 8))) (exists ((y (_ BitVec 8))) (bvult x y))))
(check-sat)
