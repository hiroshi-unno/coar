; E2-A  expected: unsat   (test T2: every linearisation is sat, see c_linear*)
;
; Abstract model: two devices on different radio platforms must meet on a common channel
; without any prior communication (the rendezvous problem of ad-hoc / cognitive radio).
;   Usable1 c : channel c is usable by device 1 (local interference, regulation)   (abstract: Ok1)
;   Usable2 c : channel c is usable by device 2                                    (abstract: Ok2)
; Contract Phi (abstraction of an interference model): of any two adjacent channels at
;   least one is usable, on each device.
; Both devices receive the same seed i (e.g. a shared clock slot). Unimplemented components Dev1, Dev2
; choose a channel each; Dev1 can sense only Usable1, Dev2 only Usable2.
; Spec S: both pick the same channel, and it is usable on at least one device.
;
; Why unsat: S forces Dev1(i) and Dev2(i) to be the same singleton. Its element is
; g1(Usable1, i) on one side and g2(Usable2, i) on the other; equality under every
; interpretation forces both to be a function c(i) of i alone. The adversary then makes
; c(0) unusable on both devices (Phi still holds). For every *fixed* interpretation a
; solution exists (pick a constant usable channel), so no single interpretation refutes
; the instance: the refutation ranges over solutions, as in DQBF.
; DQBF analogue: forall x1 x2. exists y1(x1) y2(x2). y1 = y2 /\ (y1 = x1 \/ y2 = x2).
(set-logic DQHORN)
(declare-forall-fun Usable1 (Int) Bool)
(declare-forall-fun Usable2 (Int) Bool)
(define-fun Phi () Bool (and
  (forall ((c Int)) (or (Usable1 c) (Usable1 (+ c 1))))
  (forall ((c Int)) (or (Usable2 c) (Usable2 (+ c 1))))))
(define-fun S ((c1 Int) (c2 Int)) Bool (and (= c1 c2) (or (Usable1 c1) (Usable2 c2))))
(declare-dep-exists-fun Dev1 (Usable1) (Int Int) Bool)
(declare-dep-exists-fun Dev2 (Usable2) (Int Int) Bool)
(assert (forall ((i Int)) (=> Phi (exists ((c1 Int)) (Dev1 i c1)))))
(assert (forall ((i Int)) (=> Phi (exists ((c2 Int)) (Dev2 i c2)))))
(assert (forall ((i Int) (c1 Int) (c2 Int)) (=> (and Phi (Dev1 i c1) (Dev2 i c2)) (S c1 c2))))
