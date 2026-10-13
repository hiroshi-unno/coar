; Expected: sat.
;
; Two models, written with division by zero as the open term.  Where `div 0 0` is 0 the first clause
; forces P 0 and the second is vacuous; where it is not, P may be empty.  The single formula
; `P(x) := (div 0 0 = 0) /\\ x = 0` satisfies both clauses in every model, so this is satisfiable
; under every reading and separates nothing -- it is the control for the twin whose second clause is an unconditional negative literal.
;
; A solution must hold in every model of the background theory, so an open term -- one whose value
; the theory does not fix -- is quantified universally along with the model.  Choosing a value for
; it is choosing the answer, which in a verification setting means proving a program correct on the
; strength of a decision the verifier made for its own convenience.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (=> (= (div 0 0) 0) (P 0)))
(assert (=> (and (not (= (div 0 0) 0)) (P 0)) false))
(check-sat)
