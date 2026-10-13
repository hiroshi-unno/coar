; E1-E(quiv)-B  expected: sat   (b_widened_sat.smt2 with the reverse implication added)
;
; Same model as b_widened_sat.smt2 (Sbx has dependency set {ValidS, ValidK}). Adds the
; equivalence-version reverse implication Phi /\ W /\ S => P, by the same recipe as parallel.smt2's third assert: take the forward safety
; assert and swap its box predicate and its consequent, keeping every other premise:
;   forward safety: Phi /\ ValidS(i) /\ Sbx(i, y) => ValidK(y)
;   reverse (added): Phi /\ ValidS(i) /\ ValidK(y) => Sbx(i, y)
; Together these pin Sbx(i, y) <=> ValidK(y) whenever ValidS(i) holds -- exactly the relation
; Sbx := ValidK(y) satisfies. It needs only ValidK (a strict subset of the dependency set
; {ValidS, ValidK}) and its totality follows from Phi (Phi guarantees some y has ValidK(y):
; take h = 0 in Phi to get ValidK(0) \/ ValidK(1)). So the answer does not change from
; b_widened_sat.smt2: both the refinement and the equivalence version are sat, by the same
; formula. This is expected once the dependency set already contains the predicate the
; system spec is stated over -- refining to it is already forced to be exact.
(set-logic DQHORN)
(declare-forall-fun ValidS (Int) Bool)
(declare-forall-fun ValidK (Int) Bool)
(define-fun Phi () Bool (forall ((h Int)) (or (ValidK h) (ValidK (+ h 1)))))
(declare-dep-exists-fun Sbx (ValidS ValidK) (Int Int) Bool)
(assert (forall ((i Int)) (=> (and Phi (ValidS i)) (exists ((y Int)) (Sbx i y)))))
(assert (forall ((i Int) (y Int)) (=> (and Phi (ValidS i) (Sbx i y)) (ValidK y))))
(assert (forall ((i Int) (y Int)) (=> (and Phi (ValidS i) (ValidK y)) (Sbx i y))))
