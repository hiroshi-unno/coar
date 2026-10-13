; Unsatisfiable.  A total predicate occurring only negatively whose body has no witness: P is
; declared total over its first argument (position 0), so every x needs some y with P(x, y), and
; every such point must satisfy x < y < x + 1, which no integer y does.  So no total P satisfies
; the clause, and the problem is unsatisfiable.  It exercises the refutation direction of the
; pre-loop elimination of such a predicate (the coordinator's eliminate_tot_preds setting):
; forall x. exists y. x < y < x + 1 is false, hence no total relation inside the body exists.
; Expected of a correct run: unsat, or no answer; never sat.
(set-logic HORN)
(declare-totp (0) P (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (P x y) (and (< x y) (< y (+ x 1))))))
(check-sat)
