; The graph translation of forall_fun_abs_sat.smt2: the universal
; function f is replaced by a universal predicate R intended as its graph.  R ranges over ALL
; relations, so at a non-functional R (say R(0,3) and R(0,-5)) the definite clauses force
; Q to contain both 3 and 5 and the goal fails: unsat, although the function version is sat.
; The repairs that work for injective maps (a universal-head goal naming the offending value)
; would need the disjunctive head R(0,z') \/ R(0,-z') here, which Horn forbids.
; expected: unsat
(set-logic DQHORN)
(declare-forall-fun R (Int Int) Bool)
(declare-dep-exists-fun P (R) (Int) Bool)
(declare-dep-exists-fun Q (R) (Int) Bool)
(assert (forall ((y Int)) (=> (R 0 y) (P y))))
(assert (forall ((y Int)) (=> (and (P y) (>= y 0)) (Q y))))
(assert (forall ((y Int)) (=> (and (P y) (< y 0)) (Q (- y)))))
(assert (forall ((z Int) (z2 Int)) (=> (and (Q z) (Q z2) (distinct z z2)) false)))
(check-sat)
