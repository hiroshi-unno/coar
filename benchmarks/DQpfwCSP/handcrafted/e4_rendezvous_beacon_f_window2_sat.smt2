; E4-F  expected: sat (by hand; PCSat times out at 60 s)   (Q-level contrast: bounded search window)
;
; Same as a_beacon_unsat but the common channel is promised within the window {i, i+1}, and
; the spec only asks for a common channel in that window. Now the beacon needs to carry only
; the two bits Usable1 i, Usable1 (i+1), and the dependency sets of E4-A suffice:
;   Dev1 := m = (if Usable1 i then 1 else 0) + 2 * (if Usable1 (i+1) then 1 else 0)
;   Dev2 := (c = i /\ (m = 1 \/ m = 3) /\ Usable2 i) \/ (c = i + 1 /\ (m = 2 \/ m = 3) /\ Usable2 (i+1))
; Under A one of the two branches applies, so Dev2 is total where required. This is the
; "bounded number of queries" reading of a bounded search: with a
; window of width N the beacon needs N bits, and the DQ-level unsat of E4-A is the N = infinity
; case.
(set-logic DQHORN)
(declare-forall-fun Usable1 (Int) Bool)
(declare-forall-fun Usable2 (Int) Bool)
(define-fun A ((i Int) (g Int)) Bool (and (<= i g) (<= g (+ i 1)) (Usable1 g) (Usable2 g)))
(define-fun S ((i Int) (c Int)) Bool (and (<= i c) (<= c (+ i 1)) (Usable1 c) (Usable2 c)))
(declare-dep-exists-fun Dev1 (Usable1) (Int Int) Bool)
(declare-dep-exists-fun Dev2 (Usable2) (Int Int Int) Bool)
(assert (forall ((i Int) (g Int)) (=> (A i g) (exists ((m Int)) (Dev1 i m)))))
(assert (forall ((i Int) (g Int) (m Int)) (=> (and (A i g) (Dev1 i m)) (exists ((c Int)) (Dev2 i m c)))))
(assert (forall ((i Int) (g Int) (m Int) (c Int)) (=> (and (A i g) (Dev1 i m) (Dev2 i m c)) (S i c))))
