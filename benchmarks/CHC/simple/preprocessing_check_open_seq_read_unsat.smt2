; unsat: a read of the empty sequence is a value the theory leaves open; in every model where it
; is not 0 no interpretation of P satisfies both clauses, and an unsat answer needs only one such
; model.  The preprocessing check must report the derived false unchecked, never failed.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x (seq.nth (as seq.empty (Seq Int)) 0)) (P x))))
(assert (forall ((y Int)) (=> (P y) (= y 0))))
(check-sat)
