; One parametric datatype instantiated twice, (Lst Int) and (Lst Bool).
; Until 2026-09-06 both instantiations shared the datatype's sort parameters and type inference
; failed with "unification failure: int = bool"; constructors now get fresh parameters per
; occurrence.  Expected: sat.
(set-logic HORN)
(declare-datatypes ((Lst 1)) ((par (T) ((nil) (cons (hd T) (tl (Lst T)))))))
(declare-fun P ((Lst Int)) Bool)
(declare-fun Q ((Lst Bool)) Bool)
(assert (forall ((l (Lst Int))) (=> (= l nil) (P l))))
(assert (forall ((l (Lst Int))) (=> (and (P l) (not (= l nil))) false)))
(assert (forall ((b (Lst Bool))) (=> (= b (cons true nil)) (Q b))))
(assert (forall ((b (Lst Bool))) (=> (and (Q b) (= b nil)) false)))
(check-sat)
