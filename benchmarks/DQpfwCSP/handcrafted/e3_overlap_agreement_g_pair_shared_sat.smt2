; E3-G-shared  expected: sat   (the sat side of the pair: a predicate shared by BOTH devices allows agreement)
;
; Abstract model: two devices must agree on a channel usable under Q2. In g_pair_shared_sat both sense Q2
; (Dev1 -> {Q1,Q2}, Dev2 -> {Q2,Q3}); in g_pair_disjoint_unsat neither does (Dev1 -> {Q1}, Dev2 -> {Q3}).
; No communication; both receive the seed i. Phi: adjacency for Q2 only.
; Solution: Dev1 := Dev2 := c = (if Q2 i then i else i + 1). Both templates must mention Q2.
; This is a sat instance whose solution needs the shared dependency; contrast with g_pair_disjoint_unsat.
; PCSat: expected to time out (the witness needs Q2, which the head-exists Skolem function cannot take).
(set-logic DQHORN)
(declare-forall-fun Q1 (Int) Bool)
(declare-forall-fun Q2 (Int) Bool)
(declare-forall-fun Q3 (Int) Bool)
(define-fun Phi () Bool (forall ((h Int)) (or (Q2 h) (Q2 (+ h 1)))))
(define-fun S ((c1 Int) (c2 Int)) Bool (and (= c1 c2) (Q2 c1)))
(declare-dep-exists-fun Dev1 (Q1 Q2) (Int Int) Bool)
(declare-dep-exists-fun Dev2 (Q2 Q3) (Int Int) Bool)
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev1 i c)))))
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev2 i c)))))
(assert (forall ((i Int) (c1 Int) (c2 Int)) (=> (and Phi (Dev1 i c1) (Dev2 i c2)) (S c1 c2))))
