; unsat: in every model where (div 5 0) is not 0 no interpretation of P satisfies both clauses,
; and an unsat answer needs only one such model.  The preprocessor derives false, which follows
; in those models and not in the one where (div 5 0) = 0, so the solution checker's question
; "does it follow in every model" is answered no; that is no accusation, and the preprocessing
; check must report it unchecked, never failed.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x (div 5 0)) (P x))))
(assert (forall ((y Int)) (=> (P y) (= y 0))))
(check-sat)
