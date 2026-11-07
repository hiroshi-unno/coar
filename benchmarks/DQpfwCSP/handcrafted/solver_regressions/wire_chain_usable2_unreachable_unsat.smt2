; expected: unsat (by hand)
;
; The twin of ../e2_agreement_b_wire_sat.smt2 in the other direction: device 1's channel c1
; is still wired to device 2, but the specification now asks that the common channel be
; usable by device 2. Dev1 chooses c1 knowing only Usable1, and Dev2 must answer c2 = c1, so
; Usable2 can be the point hole at the channel Dev1 picks for i (false there and nowhere else,
; which keeps the adjacency contract), and then no Dev2 meets the specification.
;
; The refutation reads each functional predicate as a function and Dev2's input as Dev1's
; output, f2(f1(i, Usable1), i, Usable2): it pins that a wired argument is the composed
; witness, while e2_agreement_b_wire_sat pins that it is not a value fixed before i.
(set-logic DQHORN)
(declare-forall-fun Usable1 (Int) Bool)
(declare-forall-fun Usable2 (Int) Bool)
(define-fun Phi ((i Int)) Bool (and
  (or (Usable1 i) (Usable1 (+ i 1)))
  (forall ((c Int)) (or (Usable2 c) (Usable2 (+ c 1))))))
(define-fun S ((c1 Int) (c2 Int)) Bool (and (= c1 c2) (Usable2 c2)))
(declare-dep-exists-fun Dev1 (Usable1) (Int Int) Bool)
(declare-dep-exists-fun Dev2 (Usable2) (Int Int Int) Bool)
(assert (forall ((i Int)) (=> (Phi i) (exists ((c1 Int)) (Dev1 i c1)))))
(assert (forall ((i Int) (c1 Int)) (=> (and (Phi i) (Dev1 i c1)) (exists ((c2 Int)) (Dev2 i c1 c2)))))
(assert (forall ((i Int) (c1 Int) (c2 Int)) (=> (and (Phi i) (Dev1 i c1) (Dev2 i c1 c2)) (S c1 c2))))
