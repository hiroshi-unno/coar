; E2-B  expected: sat   (E2-A plus a wire: device 1 announces its channel to device 2)
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
; Here Dev2 additionally receives c1 (a beacon from device 1). Solution: Dev2 := c2 = c1,
; Dev1 := ite(Usable1 i, c1 = i, c1 = i + 1). The unsat of E2-A corresponds exactly to the
; missing communication channel.
; Current implementation: times out (head-exists Skolem function ignores forall-funs).
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
