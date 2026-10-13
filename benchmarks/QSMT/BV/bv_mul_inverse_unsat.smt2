; Not every bit-vector has a multiplicative inverse: an even x has none, since
; x*y is even for every y while 1 is odd.  So forall x. exists y. x * y = 1 is
; false.  Exercises the disequality rule and the projection's fallback.
(set-logic BV)
(assert (forall ((x (_ BitVec 4))) (exists ((y (_ BitVec 4))) (= (bvmul x y) (_ bv1 4)))))
(check-sat)
