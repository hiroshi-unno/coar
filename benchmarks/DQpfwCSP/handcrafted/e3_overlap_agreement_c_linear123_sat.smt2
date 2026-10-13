; E3-C123  expected: sat   (E3-A linearised: Dev1 keeps {Q1,Q2}, Dev2 and Dev3 get {Q1,Q2,Q3}; rule A)
;
; Abstract model: e2 (rendezvous) with three devices and OVERLAPPING sensing. Device k senses two of
; the three usability predicates Q1, Q2, Q3 (platform-dependent; unknown at design time):
;   Dev1 -> {Q1, Q2},  Dev2 -> {Q2, Q3},  Dev3 -> {Q3, Q1}      (pairwise incomparable, pairwise overlapping)
; No communication. All three receive the seed i. Phi: of any two adjacent channels at least one is
; usable, for each predicate. Spec S: all three choose the same channel and it is usable under at
; least one predicate.
; Linearisation enlarges each dependency set to the union of the sets before it in the order
; Dev1 < Dev2 < Dev3. The other five orders are symmetric.
; Solution: Dev1 := c = (if Q1 i then i else i + 1)  (deterministic, usable under Q1 by Phi);
;           Dev2 := Dev3 := the same formula (they may now mention Q1).
; PCSat: expected to time out: the witness of the existence clauses needs Q1, which the head-exists
; Skolem function cannot take as an argument.
(set-logic DQHORN)
(declare-forall-fun Q1 (Int) Bool)
(declare-forall-fun Q2 (Int) Bool)
(declare-forall-fun Q3 (Int) Bool)
(define-fun Phi () Bool (and
  (forall ((h Int)) (or (Q1 h) (Q1 (+ h 1))))
  (forall ((h Int)) (or (Q2 h) (Q2 (+ h 1))))
  (forall ((h Int)) (or (Q3 h) (Q3 (+ h 1))))))
(define-fun S ((c1 Int) (c2 Int) (c3 Int)) Bool (and (= c1 c2) (= c2 c3) (or (Q1 c1) (Q2 c1) (Q3 c1))))
(declare-dep-exists-fun Dev1 (Q1 Q2) (Int Int) Bool)
(declare-dep-exists-fun Dev2 (Q1 Q2 Q3) (Int Int) Bool)
(declare-dep-exists-fun Dev3 (Q1 Q2 Q3) (Int Int) Bool)
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev1 i c)))))
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev2 i c)))))
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev3 i c)))))
(assert (forall ((i Int) (c1 Int) (c2 Int) (c3 Int)) (=> (and Phi (Dev1 i c1) (Dev2 i c2) (Dev3 i c3)) (S c1 c2 c3))))
