; E1-D(inst)-B  expected: sat   (b_widened_sat.smt2 with Phi instantiated at h := i)
;
; Same model as b_widened_sat.smt2 (Sbx has dependency set {ValidS, ValidK}). Phi's
; universal quantifier over h is replaced by the single instance at h = i, the only point
; the known solution reads: PhiInst(i) := ValidK(i) \/ ValidK(i + 1).
; Because Phi implies PhiInst(i) for every i (Phi is the conjunction of PhiInst(h) over all
; h), this file's premise is weaker than the original's, so it is a *harder* obligation
; (more ValidK-interpretations satisfy the premise): if this instantiated, quantifier-free
; version is sat, the original (with the full universally quantified Phi) is sat too, by
; the same Sbx. The converse does not hold in general -- an instance can be unsat while the
; quantified original stays sat, if the witness needed Phi at a point other than i.
; Solution: Sbx := (ValidK i /\ y = i) \/ (~ValidK i /\ y = i + 1), unchanged from
; b_widened_sat.smt2; it only ever queries ValidK at h = i, matching the instantiation point.
; Purpose: contrast the Z3-facing quantifier-free premise against the quantified Phi, since
; b_widened_sat.smt2 times out and sat-side timeouts had been attributed partly to
; array-quantifiers reaching Z3 through Phi (as well as the head-Skolem gap).
(set-logic DQHORN)
(declare-forall-fun ValidS (Int) Bool)
(declare-forall-fun ValidK (Int) Bool)
(define-fun PhiInst ((i Int)) Bool (or (ValidK i) (ValidK (+ i 1))))
(declare-dep-exists-fun Sbx (ValidS ValidK) (Int Int) Bool)
(assert (forall ((i Int)) (=> (and (PhiInst i) (ValidS i)) (exists ((y Int)) (Sbx i y)))))
(assert (forall ((i Int) (y Int)) (=> (and (PhiInst i) (ValidS i) (Sbx i y)) (ValidK y))))
