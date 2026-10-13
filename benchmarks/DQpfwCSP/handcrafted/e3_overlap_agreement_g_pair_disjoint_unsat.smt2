; E3-G-disjoint  expected: unsat   (the unsat side of the pair; rule C, as E2-A)
;
; Abstract model: two devices must agree on a channel usable under Q2. In g_pair_shared_sat both sense Q2
; (Dev1 -> {Q1,Q2}, Dev2 -> {Q2,Q3}); in g_pair_disjoint_unsat neither does (Dev1 -> {Q1}, Dev2 -> {Q3}).
; No communication; both receive the seed i. Phi: adjacency for Q2 only.
; Why unsat: S forces one singleton {c} with c = f1(Q1) = f2(Q3) for all Q1, Q3, hence constant;
; the adversary takes Q2 = Z \ {c(i)} (adjacency holds) and S fails.
(set-logic DQHORN)
(declare-forall-fun Q1 (Int) Bool)
(declare-forall-fun Q2 (Int) Bool)
(declare-forall-fun Q3 (Int) Bool)
(define-fun Phi () Bool (forall ((h Int)) (or (Q2 h) (Q2 (+ h 1)))))
(define-fun S ((c1 Int) (c2 Int)) Bool (and (= c1 c2) (Q2 c1)))
(declare-dep-exists-fun Dev1 (Q1) (Int Int) Bool)
(declare-dep-exists-fun Dev2 (Q3) (Int Int) Bool)
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev1 i c)))))
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev2 i c)))))
(assert (forall ((i Int) (c1 Int) (c2 Int)) (=> (and Phi (Dev1 i c1) (Dev2 i c2)) (S c1 c2))))
