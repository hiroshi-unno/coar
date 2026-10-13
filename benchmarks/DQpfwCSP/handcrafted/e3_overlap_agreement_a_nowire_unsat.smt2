; E3-A  expected: unsat   (test T2: every linearisation is sat, see c_linear123_sat; rule C)
;
; Abstract model: e2 (rendezvous) with three devices and OVERLAPPING sensing. Device k senses two of
; the three usability predicates Q1, Q2, Q3 (platform-dependent; unknown at design time):
;   Dev1 -> {Q1, Q2},  Dev2 -> {Q2, Q3},  Dev3 -> {Q3, Q1}      (pairwise incomparable, pairwise overlapping)
; No communication. All three receive the seed i. Phi: of any two adjacent channels at least one is
; usable, for each predicate. Spec S: all three choose the same channel and it is usable under at
; least one predicate.
;
; Why unsat (e2's proof, one step longer): S forces Dev1(i), Dev2(i), Dev3(i) to be one singleton
; {c}, with c = f1(Q1,Q2) = f2(Q2,Q3) = f3(Q3,Q1) under every interpretation. Varying Q1 alone leaves
; f2 unchanged, so f1 depends on Q2 only; varying Q3 alone shows f2 depends on Q2 only; so
; f1 = f2 = h(Q2); then f3(Q3,Q1) = h(Q2) for all Q2 forces a constant c*. The adversary takes
; Q1 = Q2 = Q3 = Z \ {c*(i)} (adjacency holds) and S fails. Lesson: a predicate shared by every
; PAIR of devices does not give consensus; only one shared by ALL would. The dependency poset is an
; overlapping antichain, a shape e2/e4 (disjoint antichains) do not have.
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
(declare-dep-exists-fun Dev2 (Q2 Q3) (Int Int) Bool)
(declare-dep-exists-fun Dev3 (Q3 Q1) (Int Int) Bool)
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev1 i c)))))
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev2 i c)))))
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev3 i c)))))
(assert (forall ((i Int) (c1 Int) (c2 Int) (c3 Int)) (=> (and Phi (Dev1 i c1) (Dev2 i c2) (Dev3 i c3)) (S c1 c2 c3))))
