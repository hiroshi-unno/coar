; sat (cb = 63).  Z3 5.1.0 does not answer within 30 s: the word is read back
; through (_ int_to_bv 64) (ubv_to_int ...), a round trip that is the identity
; at one width.  With the round trip removed it answers in about 0.3 s.  The
; shape is a Thrust-emitted popcount step (an Int word, a bit set by bvor and
; bvshl, read back as an Int and converted again).
(set-logic ALL)
(declare-fun cb () (_ BitVec 64))
(assert (let ((a!1 (ubv_to_int (bvor #x0000000000000041 (bvshl #x0000000000000001 cb)))))
  (not (= 0 (ubv_to_int (bvand (bvlshr ((_ int_to_bv 64) a!1) #x000000000000003f)
                               #x0000000000000001))))))
(check-sat)
