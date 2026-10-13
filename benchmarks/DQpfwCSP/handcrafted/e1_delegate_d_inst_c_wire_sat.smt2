; E1-D(inst)-C  expected: sat   (c_wire_sat.smt2 with Phi instantiated at h := i)
;
; Same model as c_wire_sat.smt2. Phi is instantiated at h := i, the only point the wire
; Broker and the solution read: PhiInst(i) := ValidK(i) \/ ValidK(i + 1). As in
; d_inst_b_widened_sat.smt2, Phi implies PhiInst(i), so this premise is weaker and the
; obligation is harder (more ValidK-interpretations satisfy it); sat here entails sat in
; c_wire_sat.smt2, not conversely.
; Solution: Sbx := (b /\ y = i) \/ (~b /\ y = i + 1), unchanged.
(set-logic DQHORN)
(declare-forall-fun ValidS (Int) Bool)
(declare-forall-fun ValidK (Int) Bool)
(define-fun PhiInst ((i Int)) Bool (or (ValidK i) (ValidK (+ i 1))))
(define-fun Broker ((i Int) (b Bool)) Bool (= b (ValidK i)))
(declare-dep-exists-fun Sbx (ValidS) (Int Bool Int) Bool)
(assert (forall ((i Int) (b Bool))
  (=> (and (PhiInst i) (ValidS i) (Broker i b)) (exists ((y Int)) (Sbx i b y)))))
(assert (forall ((i Int) (b Bool) (y Int))
  (=> (and (PhiInst i) (ValidS i) (Broker i b) (Sbx i b y)) (ValidK y))))
