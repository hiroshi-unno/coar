; int_to_bv 8 of the signed value of a 16-bit vector keeps its low 8 bits:
; #x0100 and #x0000 both become #x00, so the two sides are equal and the
; assertion set is unsatisfiable.  Replacing int_to_bv_8 (sbv_to_int t) by t
; regardless of t's width turns the 8-bit equation into y = z (sat).
(set-logic ALL)
(declare-fun y () (_ BitVec 16))
(declare-fun z () (_ BitVec 16))
(assert (= y #x0100))
(assert (= z #x0000))
(assert (not (= ((_ int_to_bv 8) (sbv_to_int y)) ((_ int_to_bv 8) (sbv_to_int z)))))
(check-sat)
