; A universally quantified function into the forall-sort with a trait law:
; fresh : a -> a with fresh(x) != x as a premise.  Q(x, y) := (x != y) is a
; solution.  Without the law a singleton interpretation (fresh x = x) refutes it: unsat.
; expected: sat
(set-logic DQHORN)
(declare-forall-sort a)
(declare-forall-fun fresh (a) a)
(declare-fun Q (a a) Bool)
(assert (forall ((x a)) (=> (distinct (fresh x) x) (Q x (fresh x)))))
(assert (forall ((x a) (y a)) (=> (and (Q x y) (= x y)) false)))
(check-sat)
