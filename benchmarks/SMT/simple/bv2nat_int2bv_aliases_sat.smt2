; an 8-bit x whose unsigned value is 200 and whose int2bv-of-(value+56) is zero
(set-logic ALL)
(declare-const x (_ BitVec 8))
(assert (= (bv2nat x) 200))
(assert (= ((_ int2bv 8) (+ (bv2nat x) 56)) #x00))
(check-sat)
