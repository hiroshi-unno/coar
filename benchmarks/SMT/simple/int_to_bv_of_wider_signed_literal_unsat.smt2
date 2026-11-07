; int_to_bv 8 of the signed value of the 16-bit #x0100 (256) is #x00, so the
; disequation is false.  The same rewrite as in int_to_bv_of_wider_signed_unsat
; leaves a 16-bit term where an 8-bit one belongs.
(set-logic ALL)
(declare-fun y () (_ BitVec 16))
(assert (= y #x0100))
(assert (not (= ((_ int_to_bv 8) (sbv_to_int y)) #x00)))
(check-sat)
