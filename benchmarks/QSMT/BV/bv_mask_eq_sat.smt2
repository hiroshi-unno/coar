; y = c witnesses forall c. exists y. y & 0x0F = c & 0x0F.  An equality that
; constrains only the bits under a mask is solved bit-block-wise rather than
; by inverting a coefficient: the masked-off bits of y stay free.
(set-logic BV)
(assert (forall ((c (_ BitVec 8))) (exists ((y (_ BitVec 8))) (= (bvand y (_ bv15 8)) (bvand c (_ bv15 8))))))
(check-sat)
