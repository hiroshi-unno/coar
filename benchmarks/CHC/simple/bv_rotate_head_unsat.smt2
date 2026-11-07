; rotating #b1001 left by one gives #b0011
(set-logic HORN)
(declare-fun P ((_ BitVec 4)) Bool)
(assert (forall ((x (_ BitVec 4))) (=> (= x #b1001) (P ((_ rotate_left 1) x)))))
(assert (forall ((y (_ BitVec 4))) (=> (and (P y) (= y #b0011)) false)))
(check-sat)
