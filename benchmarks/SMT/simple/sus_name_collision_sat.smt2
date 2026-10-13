; expected: sat
; A parametric instantiation is distinct from a lookalike nullary user sort.
(set-logic ALL)
(declare-sort S 1)
(declare-sort |S<int>| 0)
(declare-const c |S<int>|)
(declare-const d |S<int>|)
(assert (forall ((x (S Int)) (y (S Int))) (= x y)))
(assert (distinct c d))
(check-sat)
