; The dependency set changes the verdict: P is declared with the
; EMPTY dependency set, so its solution may not mention the universal predicate R, and the
; clauses R x => P x, P x => R x force P = R for every R.  No R-independent P does that,
; so the problem is unsat.  With P depending on R (dep_full_set_sat.smt2) it is sat.  Both
; clauses are strictly Horn (one positive predicate literal each), so the separation lives in
; the strict fragment whose propositional shadow is DQHORN.  expected: unsat
(set-logic DQHORN)
(declare-forall-fun R (Int) Bool)
(declare-dep-exists-fun P () (Int) Bool)
(assert (forall ((x Int)) (=> (R x) (P x))))
(assert (forall ((x Int)) (=> (P x) (R x))))
(check-sat)
