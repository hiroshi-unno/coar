; Satisfiable.  A functional predicate P over the reals whose clauses are
;   P(y) => 2y = 1        P(y) => y >= 0
; A solution: P(y) := (y = 1/2), total and single-valued.  No integer fits.
;
; What the file is for: before the CEGIS loop such a predicate is eliminated by
; playing the strategy game on exists y. 2y = 1 /\ y >= 0 over the reals.  The
; game once searched the refuter's moves among the integers only (its Herbrand
; variables were declared Int whatever the theory), so the refuter won and the
; problem was answered unsat.  Preprocessing off reaches that elimination.
(set-logic HORN)
(declare-fnp P (Real) Bool)
(assert (forall ((y Real)) (=> (P y) (= (* 2.0 y) 1.0))))
(assert (forall ((y Real)) (=> (P y) (>= y 0.0))))
(check-sat)
