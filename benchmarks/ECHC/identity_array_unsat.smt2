; An array-sort instance of theory sensitivity: the verdict depends on which models of the
; array theory are admitted.  P must be non-empty (the head existential) and hold only
; of the identity array.
; Over the standard arrays (full function spaces) it is satisfiable: P := { a | forall i. a[i] = i }.
; In the finite-support arrays, a model of the extensional array axioms in which every array differs
; from a constant array at finitely many indices, no identity array exists, so P has no member and
; the head existential fails.  This repository's definition asks for a solution in every model of
; the background theory, and the SMT-LIB arrays theory admits the finite-support arrays, so the
; verdict it defines is UNSATISFIABLE; over the standard arrays it would be sat.  expected: unsat
(set-logic HORN)
(declare-fun P ((Array Int Int)) Bool)
(assert (exists ((a (Array Int Int))) (P a)))
(assert (forall ((a (Array Int Int)) (i Int)) (=> (P a) (= (select a i) i))))
(check-sat)
