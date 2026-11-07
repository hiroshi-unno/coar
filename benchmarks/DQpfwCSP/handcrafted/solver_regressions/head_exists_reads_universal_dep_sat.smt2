; A head existential whose body reads a universal function outside the dependency set of the unknown
; under it.  Satisfiable: P := true, G(X) := "X is non-empty", and the witness y is a point of X.
; Restricting the witness to P's dependency set, which is empty, made it a constant c, and
; X := {c + 1} then refuted every solution.
(set-logic HORN)
(declare-forall-fun X (Int) Bool)
(declare-dep-exists-fun P () (Int) Bool)
(declare-dep-exists-fun G (X) () Bool)
(assert (forall ((b Int)) (=> (X b) G)))
(assert (=> G (exists ((y Int)) (and (P y) (X y)))))
(check-sat)
