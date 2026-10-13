; E1-E(quiv)-C  expected: unsat   (c_wire_sat.smt2 with the reverse implication added)
;
; Same model as c_wire_sat.smt2. Adds the equivalence-version reverse implication, by the
; same recipe as parallel.smt2's third assert (swap the box predicate and the consequent of
; the forward safety assert, keeping every other premise, here including the wire Broker):
;   forward safety: Phi /\ ValidS(i) /\ Broker(i, b) /\ Sbx(i, b, y) => ValidK(y)
;   reverse (added): Phi /\ ValidS(i) /\ Broker(i, b) /\ ValidK(y) => Sbx(i, b, y)
; Together these force Sbx(i, b, y) <=> ValidK(y) whenever ValidS(i) /\ Broker(i, b) holds.
; Why unsat: fix i with ValidS(i) and let b = ValidK(i) (as Broker forces). Sbx's vocabulary
; is {ValidS, i, b, y} -- it can mention ValidK only through b, which reports ValidK(i) and
; nothing about ValidK at any other point, and ValidK is otherwise unconstrained at a y
; unrelated to i (Phi only ties ValidK(h) to ValidK(h + 1), not to an arbitrary y). So no
; formula over {ValidS, i, b, y} can equal ValidK(y) for every y: pick y with
; y != i - 1, i, i + 1 and an interpretation of ValidK making ValidK(y) disagree with
; whatever Sbx(i, b, y) evaluates to; Sbx cannot detect that disagreement since it has no
; access to ValidK(y). This confirms the claim that E1-C becomes unsat under the equivalence version, unlike its sat
; refinement-version answer: the single wire bit that made refinement work (E1-C, replacing
; the ValidK dependency by b = ValidK(i)) is exactly the information equivalence's
; completeness requirement needs at *every* y, not just at i.
; Current implementation: unsat side, expect timeout as with a_nodep_unsat.smt2.
(set-logic DQHORN)
(declare-forall-fun ValidS (Int) Bool)
(declare-forall-fun ValidK (Int) Bool)
(define-fun Phi () Bool (forall ((h Int)) (or (ValidK h) (ValidK (+ h 1)))))
(define-fun Broker ((i Int) (b Bool)) Bool (= b (ValidK i)))
(declare-dep-exists-fun Sbx (ValidS) (Int Bool Int) Bool)
(assert (forall ((i Int) (b Bool))
  (=> (and Phi (ValidS i) (Broker i b)) (exists ((y Int)) (Sbx i b y)))))
(assert (forall ((i Int) (b Bool) (y Int))
  (=> (and Phi (ValidS i) (Broker i b) (Sbx i b y)) (ValidK y))))
(assert (forall ((i Int) (b Bool) (y Int))
  (=> (and Phi (ValidS i) (Broker i b) (ValidK y)) (Sbx i b y))))
