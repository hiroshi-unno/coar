; E1-C  expected: sat   (E1-A plus a wire from a broker with a given definition)
;
; Same model as a_nodep_unsat.smt2. A given component Broker (the privileged process) checks the
; handle with the kernel API and forwards the single boolean b = ValidK i to the sandbox.
; The sandboxed component still references only ValidS, but can branch on the wire value.
; Solution: Sbx := (b /\ y = i) \/ (~b /\ y = i + 1).
; This shows that E1's dependency on ValidK is replaceable by one wire (the former wire test, since
; dropped: for a single unimplemented component the wire-vs-predicate difference is T1 itself).
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
