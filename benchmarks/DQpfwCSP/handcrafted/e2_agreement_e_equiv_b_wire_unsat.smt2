; E2-E(quiv)-B  expected: unsat   (b_wire_sat.smt2 with the multi-component reverse implication)
;
; Same model as b_wire_sat.smt2 (Dev2 additionally receives c1 on a wire). E2 has two black
; boxes, so the reverse cannot be written per-box the way E1 does:
; reach_3 = Dev1(i, c1) /\ Dev2(i, c1, c2) shares c1 between both boxes, and
; only c2 (alongside i) is the system's externally observed output, so the reverse
; existentially re-introduces a fresh witness for the other box's output instead of reusing
; the outer c1 already bound by S:
;   forward safety: Phi /\ Dev1(i, c1) /\ Dev2(i, c1, c2) => S(c1, c2)
;   reverse (added): Phi /\ S(c1, c2) => exists c1'. Dev1(i, c1') /\ Dev2(i, c1', c2)
; (c1 stays bound by the outer forall, matching S's own argument; c1' is the fresh
; existential playing the role of "o_1" in the exists o_1, ..., o_{n-1} form of the definition.)
;
; Why unsat: forward safety together with the totality asserts already force
; Dev2(i, c1', c2) to require c1' = c2 whenever Dev1(i, c1') holds (S forces c1 = c2), so the
; reverse's conclusion needs Dev1(i, c2) to hold. The reverse's premise only requires
; S(c1, c2) for *some* c1, i.e. Usable1(c2) \/ Usable2(c2), for every i and every such c2 --
; including c2 where Usable1(c2) is false but Usable2(c2) is true (Phi constrains Usable1 and
; Usable2 separately, not their relation to each other, so the adversary is free to choose
; them this way). Dev1's vocabulary is {Usable1}, so it cannot detect that Usable2(c2) is
; what justifies usability there; no Usable1-only formula can be forced true at exactly
; those points without breaking Dev2's totality elsewhere (if Dev1 accepted every c1
; regardless of Usable1, Dev2 would have to accept every c1 too, but Dev2 only has
; {Usable2} and cannot certify c1 = c2 unconditionally without breaking forward safety at
; points where Usable1(c1) holds and Usable2(c1) does not). This is the same diagonalisation
; as a_nowire_unsat.smt2's argument, reimported through the equivalence version's
; completeness requirement: the wire that made b_wire_sat.smt2 sat under refinement only had
; to cover the outputs Dev1 actually produces; equivalence has to cover every output S
; admits, including ones a Usable1-only Dev1 cannot recognise.
; Current implementation: unsat side, expect timeout as with a_nowire_unsat.smt2.
(set-logic DQHORN)
(declare-forall-fun Usable1 (Int) Bool)
(declare-forall-fun Usable2 (Int) Bool)
(define-fun Phi () Bool (and
  (forall ((c Int)) (or (Usable1 c) (Usable1 (+ c 1))))
  (forall ((c Int)) (or (Usable2 c) (Usable2 (+ c 1))))))
(define-fun S ((c1 Int) (c2 Int)) Bool (and (= c1 c2) (or (Usable1 c1) (Usable2 c2))))
(declare-dep-exists-fun Dev1 (Usable1) (Int Int) Bool)
(declare-dep-exists-fun Dev2 (Usable2) (Int Int Int) Bool)
(assert (forall ((i Int)) (=> Phi (exists ((c1 Int)) (Dev1 i c1)))))
(assert (forall ((i Int) (c1 Int)) (=> (and Phi (Dev1 i c1)) (exists ((c2 Int)) (Dev2 i c1 c2)))))
(assert (forall ((i Int) (c1 Int) (c2 Int)) (=> (and Phi (Dev1 i c1) (Dev2 i c1 c2)) (S c1 c2))))
(assert (forall ((i Int) (c1 Int) (c2 Int)) (=> (and Phi (S c1 c2))
  (exists ((c1p Int)) (and (Dev1 i c1p) (Dev2 i c1p c2))))))
