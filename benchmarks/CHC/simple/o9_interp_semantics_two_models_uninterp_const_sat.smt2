; Expected: sat.
;
; Two models, written with an uninterpreted constant.  The control for the twin whose second clause is an unconditional negative literal: the formula
; `P(x) := (u = 0) /\\ x = 0` satisfies both clauses in every model.
;
; A solution must hold in every model of the background theory, so an open term -- one whose value
; the theory does not fix -- is quantified universally along with the model.  Choosing a value for
; it is choosing the answer, which in a verification setting means proving a program correct on the
; strength of a decision the verifier made for its own convenience.
(set-logic HORN)
(declare-fun u () Int)
(declare-fun P (Int) Bool)
(assert (=> (= u 0) (P 0)))
(assert (=> (and (not (= u 0)) (P 0)) false))
(check-sat)
