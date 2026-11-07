; bv2nat and (_ int2bv n) are z3's and cvc5's names for ubv_to_int and
; (_ int_to_bv n); int2bv takes the integer modulo 2^n
(set-logic ALL)
(assert (not (and (= (bv2nat #xff) 255)
                  (= ((_ int2bv 8) 257) #x01)
                  (= ((_ int2bv 8) (- 1)) #xff)
                  (= (bv2nat ((_ int2bv 4) 21)) (ubv_to_int ((_ int_to_bv 4) 21))))))
(check-sat)
