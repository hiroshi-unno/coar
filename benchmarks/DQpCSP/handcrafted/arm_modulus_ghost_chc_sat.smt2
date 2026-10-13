; POPL 2024's repair for `modulus`: the ghost parameter `_r` carries the sequences' common value
; at the probed index, so the contract is indexed by it -- `S(r, n, v)`.  Middle file of the
; triple.  expected: sat
(set-logic HORN)
(declare-fun S (Int Int Int) Bool)
(declare-fun Ans (Int Int) Bool)
(assert (forall ((r Int) (v Int)) (=> (S r 10 v) (Ans r v))))
(assert (forall ((r Int) (n Int) (v Int)) (=> (=> (= n 10) (= v r)) (S r n v))))
(assert (forall ((r Int) (z Int)) (=> (and (Ans r z) (not (= z r))) false)))
(check-sat)
