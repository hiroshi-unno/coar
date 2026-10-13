; Every even bit-vector is some other bit-vector shifted left by one, so
; masking off the low bit of x always leaves a shift target.  A shift by a
; constant is a multiplication by a power of two, i.e. an even coefficient on
; the eliminated variable, which is the case the equality rule cannot solve by
; inversion.  Z3 4.x does not terminate on this file; cvc5 answers sat.
(set-logic BV)
(assert (forall ((x (_ BitVec 8))) (exists ((y (_ BitVec 8))) (= (bvshl y (_ bv1 8)) (bvand x (_ bv254 8))))))
(check-sat)
