; No unknown predicate.  The constraint is violated by p = (pair (const 0) 0),
; so the problem is unsat, and every symbol in it is interpreted: Pair has a
; single constructor, so the projection (snd p) is total and the theory fixes
; its value.  Treating every datatype selector as interpretation-dependent --
; true only of a selector applied to the *wrong* constructor, which a
; single-constructor datatype does not have -- made the no-unknown verdict ask
; whether the universal closure is satisfiable instead of whether the formula
; is valid.  Z3 answers "unknown (incomplete (theory array))" on that closure,
; so a decided unsat was reported as unknown.
(set-logic HORN)
(declare-datatypes ((Pair 0)) (((pair (fst (Array Int Int)) (snd Int)))))
(assert (forall ((p Pair) (i Int))
  (=> (and (= (snd p) 0) (= (select (fst p) i) 0)) false)))
(check-sat)
