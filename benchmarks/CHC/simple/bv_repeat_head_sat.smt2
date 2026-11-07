; P = {#b1010} is a solution
(set-logic HORN)
(declare-fun P ((_ BitVec 4)) Bool)
(assert (forall ((x (_ BitVec 2))) (=> (= x #b10) (P ((_ repeat 2) x)))))
(assert (forall ((y (_ BitVec 4))) (=> (and (P y) (not (= y #b1010))) false)))
(check-sat)
