; E1-B  expected: sat   (E1-A with the dependency set widened to {ValidS, ValidK})
;
; Same model as a_nodep_unsat.smt2, but the sandboxed component may query the kernel API.
; Solution: Sbx := (ValidK i /\ y = i) \/ (~ValidK i /\ y = i + 1).
; Current implementation: times out, because the Skolem function of the head `exists y`
; does not take the forall-fun arrays as arguments.
(set-logic DQHORN)
(declare-forall-fun ValidS (Int) Bool)
(declare-forall-fun ValidK (Int) Bool)
(define-fun Phi () Bool (forall ((h Int)) (or (ValidK h) (ValidK (+ h 1)))))
(declare-dep-exists-fun Sbx (ValidS ValidK) (Int Int) Bool)
(assert (forall ((i Int)) (=> (and Phi (ValidS i)) (exists ((y Int)) (Sbx i y)))))
(assert (forall ((i Int) (y Int)) (=> (and Phi (ValidS i) (Sbx i y)) (ValidK y))))
