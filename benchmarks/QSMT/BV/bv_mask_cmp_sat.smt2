; y = c witnesses both conjuncts, since c & 0x0F <=u c <=u c | 0x0F: clearing
; bits can only lower an unsigned value and setting bits can only raise it.
; Both conjuncts compare a masked term against a universal, which is the
; masked-comparison shape, and the two masks pull in opposite directions so
; neither conjunct alone determines y.
(set-logic BV)
(assert (forall ((c (_ BitVec 8))) (exists ((y (_ BitVec 8))) (and (bvule (bvand y (_ bv15 8)) c) (bvule c (bvor y (_ bv15 8)))))))
(check-sat)
