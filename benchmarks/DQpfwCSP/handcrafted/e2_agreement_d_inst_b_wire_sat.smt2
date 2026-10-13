; E2-D(inst)-B  expected: sat   (b_wire_sat.smt2 with Phi instantiated at h := i)
;
; Same model as b_wire_sat.smt2. The solution Dev1 := ite(Usable1 i, c1 = i, c1 = i + 1),
; Dev2 := c2 = c1 only ever needs Usable1 at h = i; the Usable2 conjunct of Phi is not
; needed by this witness at all (Dev2 never queries Usable2, it only copies the wire c1).
; PhiInst(i) := Usable1(i) \/ Usable1(i + 1) keeps only the needed conjunct, instantiated at
; the needed point, and drops the Usable2 conjunct entirely -- a further weakening on top of
; the point instantiation, still implied by the full Phi, so sat here still entails sat in
; b_wire_sat.smt2.
(set-logic DQHORN)
(declare-forall-fun Usable1 (Int) Bool)
(declare-forall-fun Usable2 (Int) Bool)
(define-fun PhiInst ((i Int)) Bool (or (Usable1 i) (Usable1 (+ i 1))))
(define-fun S ((c1 Int) (c2 Int)) Bool (and (= c1 c2) (or (Usable1 c1) (Usable2 c2))))
(declare-dep-exists-fun Dev1 (Usable1) (Int Int) Bool)
(declare-dep-exists-fun Dev2 (Usable2) (Int Int Int) Bool)
(assert (forall ((i Int)) (=> (PhiInst i) (exists ((c1 Int)) (Dev1 i c1)))))
(assert (forall ((i Int) (c1 Int)) (=> (and (PhiInst i) (Dev1 i c1)) (exists ((c2 Int)) (Dev2 i c1 c2)))))
(assert (forall ((i Int) (c1 Int) (c2 Int)) (=> (and (PhiInst i) (Dev1 i c1) (Dev2 i c1 c2)) (S c1 c2))))
