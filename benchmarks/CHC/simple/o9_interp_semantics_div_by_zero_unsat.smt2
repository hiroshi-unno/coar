; Expected: unsat.
;
; The separator, written with division by zero as the open term.  In a model where `div 0 0` is 0 the
; first clause forces P 0 and the second forbids it, so no interpretation of P works there and the
; system has no solution.  Its twin writes the same shape with a datatype selector on the wrong
; constructor, and a third with an uninterpreted constant; all three are the same problem.
;
; A solution must hold in every model of the background theory, so an open term -- one whose value
; the theory does not fix -- is quantified universally along with the model.  Choosing a value for
; it is choosing the answer, which in a verification setting means proving a program correct on the
; strength of a decision the verifier made for its own convenience.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (=> (= (div 0 0) 0) (P 0)))
(assert (=> (P 0) false))
(check-sat)
