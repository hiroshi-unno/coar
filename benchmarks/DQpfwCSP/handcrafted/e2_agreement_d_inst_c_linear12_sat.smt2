; E2-D(inst)-C12  expected: sat   (c_linear12_sat.smt2 with Phi instantiated at h := i)
;
; Same model and linearisation as c_linear12_sat.smt2 (Dev2's dependency set widened to
; {Usable1, Usable2}). Solution: Dev1 := ite(Usable1 i, c1 = i, c1 = i + 1), Dev2 := the
; same formula over Usable1 -- both only ever query Usable1 at h = i, and neither queries
; Usable2 at all, so PhiInst(i) := Usable1(i) \/ Usable1(i + 1) (dropping the Usable2
; conjunct) suffices, exactly as in d_inst_b_wire_sat.smt2.
(set-logic DQHORN)
(declare-forall-fun Usable1 (Int) Bool)
(declare-forall-fun Usable2 (Int) Bool)
(define-fun PhiInst ((i Int)) Bool (or (Usable1 i) (Usable1 (+ i 1))))
(define-fun S ((c1 Int) (c2 Int)) Bool (and (= c1 c2) (or (Usable1 c1) (Usable2 c2))))
(declare-dep-exists-fun Dev1 (Usable1) (Int Int) Bool)
(declare-dep-exists-fun Dev2 (Usable1 Usable2) (Int Int) Bool)
(assert (forall ((i Int)) (=> (PhiInst i) (exists ((c1 Int)) (Dev1 i c1)))))
(assert (forall ((i Int)) (=> (PhiInst i) (exists ((c2 Int)) (Dev2 i c2)))))
(assert (forall ((i Int) (c1 Int) (c2 Int)) (=> (and (PhiInst i) (Dev1 i c1) (Dev2 i c2)) (S c1 c2))))
