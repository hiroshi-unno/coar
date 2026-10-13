; Expected: unsat.
;
; The same recursive query with division by zero as the open term instead of a datatype selector.
;
; A solution must hold in every model of the background theory, so an open term -- one whose value
; the theory does not fix -- is quantified universally along with the model.  Choosing a value for
; it is choosing the answer, which in a verification setting means proving a program correct on the
; strength of a decision the verifier made for its own convenience.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) (P (+ x 1)))))
(assert (forall ((x Int)) (=> (and (P x) (< x (div 0 0))) false)))
(check-sat)
