; card2_constants_sat.smt2 written with an explicit dependency set instead of ordinary
; arguments: the unknown P is declared with
; (declare-dep-exists-fun P (A B R) (a) Bool), so it may depend on the two universal
; constants A, B of the forall-sort a and on the forall-fun predicate R, and is applied in
; the clauses as (P x).  P(A, B, R, x) := (x = A) is a solution.  Until 2026-09-06 the
; front end kept only R (the dependency list was filtered by kind_map, which only Bool
; forall-funs enter), so P could not mention A or B and the answer was unsat.
; expected: sat
(set-logic DQHORN)
(declare-forall-sort a)
(declare-forall-fun A () a)
(declare-forall-fun B () a)
(declare-forall-fun R (a) Bool)
(declare-dep-exists-fun P (A B R) (a) Bool)
(assert (forall ((x a)) (=> (and (distinct A B) (= x A) (R x)) (P x))))
(assert (forall ((x a)) (=> (and (distinct A B) (P x) (= x B)) false)))
(check-sat)
