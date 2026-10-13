; A prefix that quantifies over Bool *and* bit-vectors.  The two kinds of
; variable are eliminated by different projections -- Booleans by the Boolean
; one, bit-vectors by the bit-vector one -- so this checks that a mixed
; Bool/bit-vector prefix is accepted and that the split is made per variable.
(set-logic BV)
(assert (forall ((b Bool) (x (_ BitVec 8))) (exists ((y (_ BitVec 8))) (= y (ite b x (bvnot x))))))
(check-sat)
