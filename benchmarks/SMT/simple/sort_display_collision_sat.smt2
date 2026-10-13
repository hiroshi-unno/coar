; expected: sat; uninterpreted sort instances must not be identified by their printed names.
; Built-in Int and a nullary user sort named int are different parameters.
(set-logic ALL)
(declare-sort S 1)
(declare-sort int 0)
(declare-const c (S int))
(declare-const d (S int))
(assert (forall ((x (S Int)) (y (S Int))) (= x y)))
(assert (distinct c d))
(check-sat)
