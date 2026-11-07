; int_to_bv 8 of the signed values of #x0101 and #x0000 are #x01 and #x00,
; which differ: satisfiable.  The control for int_to_bv_of_wider_signed_unsat,
; so that a fix which answers unsat for every narrowing is told apart.
(set-logic ALL)
(declare-fun y () (_ BitVec 16))
(declare-fun z () (_ BitVec 16))
(assert (= y #x0101))
(assert (= z #x0000))
(assert (not (= ((_ int_to_bv 8) (sbv_to_int y)) ((_ int_to_bv 8) (sbv_to_int z)))))
(check-sat)
