; Dependency-respecting elimination: P has the empty dependency
; set and is fed by Q, which depends on the universal R.  Semantically P(x) must hold whenever
; *some* interpretation of R makes Q(R, x) true, i.e. for every x, so the goal fails at R = {}:
; unsat.  Eliminating P by resolution as if it depended on R (P := Q := R) would turn the goal
; into R x /\ not (R x) => false and answer sat -- the analogue of unsound universal reduction /
; the need for fork resolution in DQBF.  expected: unsat
(set-logic DQHORN)
(declare-forall-fun R (Int) Bool)
(declare-dep-exists-fun Q (R) (Int) Bool)
(declare-dep-exists-fun P () (Int) Bool)
(assert (forall ((x Int)) (=> (R x) (Q x))))
(assert (forall ((x Int)) (=> (Q x) (P x))))
(assert (forall ((x Int)) (=> (and (P x) (not (R x))) false)))
(check-sat)
