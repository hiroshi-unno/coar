; E4-C12  expected: sat   (E4-A linearised as forall Usable1. exists Dev1. forall Usable2. exists Dev2)
;
; Abstract model: e2 (rendezvous of two radio devices) with a one-way link. Dev1 can send
; Dev2 a single beacon value m (one integer, i.e. one finite message) before Dev2 chooses
; the channel c; Dev2 cannot talk back. The spec is stronger than e2: c must be usable on
; BOTH devices. Dev1 senses only Usable1, Dev2 only Usable2; neither can query the other.
;   Usable1 c : channel c is usable by device 1                                    (abstract: Ok1)
;   Usable2 c : channel c is usable by device 2                                    (abstract: Ok2)
; Premise A(i, g): some channel g >= i is usable on both devices. g is a system input that
;   nobody receives; a clause-level forall g in the premise is the same as exists g, so this
;   states an existence premise without a forall-exists inside Phi so that every clause stays universal and the head-exists witness is first-order. No Phi.
; Spec S(i, c): c >= i and c is usable on both devices.
;
; Dev2 gets {Usable1, Usable2}: a two-way link, Dev2 may query Dev1's sensing at will.
; Solution: Dev1 := true;  Dev2 := i <= c /\ Usable1 c /\ Usable2 c  (witness c := g).
(set-logic DQHORN)
(declare-forall-fun Usable1 (Int) Bool)
(declare-forall-fun Usable2 (Int) Bool)
(define-fun A ((i Int) (g Int)) Bool (and (<= i g) (Usable1 g) (Usable2 g)))
(define-fun S ((i Int) (c Int)) Bool (and (<= i c) (Usable1 c) (Usable2 c)))
(declare-dep-exists-fun Dev1 (Usable1) (Int Int) Bool)
(declare-dep-exists-fun Dev2 (Usable1 Usable2) (Int Int Int) Bool)
(assert (forall ((i Int) (g Int)) (=> (A i g) (exists ((m Int)) (Dev1 i m)))))
(assert (forall ((i Int) (g Int) (m Int)) (=> (and (A i g) (Dev1 i m)) (exists ((c Int)) (Dev2 i m c)))))
(assert (forall ((i Int) (g Int) (m Int) (c Int)) (=> (and (A i g) (Dev1 i m) (Dev2 i m c)) (S i c))))
