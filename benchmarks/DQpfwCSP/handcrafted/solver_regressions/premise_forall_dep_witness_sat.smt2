; A universal written in a clause body, over an unknown that does not depend on the universal function
; the body reads.  Satisfiable: K := false, G(X) := "X is empty".  If X is empty the first clause's
; premise holds and G holds; otherwise the premise fails at a point of X, which depends on X.  Once
; answered unsat: the witness of the body universal (a point of X outside K) was restricted to K's
; dependency set, which is empty, so it was a constant c and X := {c + 1} refuted every solution.
(set-logic HORN)
(declare-forall-fun X (Int) Bool)
(declare-dep-exists-fun K () (Int) Bool)
(declare-dep-exists-fun G (X) () Bool)
(assert (=> (forall ((a Int)) (=> (X a) (K a))) G))
(assert (forall ((b Int)) (=> (and G (X b)) false)))
(check-sat)
