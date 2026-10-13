; Expected: unsat.
;
; A recursive query whose refutation needs an inductive invariant AND an open term, so it is not a
; two-line probe: P holds of every natural, and the query asks whether some such x is below the
; value of a datatype selector applied to the wrong constructor.  In a model where that value is
; positive, x = 0 refutes it.  Kept because a solver that declines the two-line probes may still
; answer here, which is what tells a genuine reading apart from a refusal to engage.
;
; A solution must hold in every model of the background theory, so an open term -- one whose value
; the theory does not fix -- is quantified universally along with the model.  Choosing a value for
; it is choosing the answer, which in a verification setting means proving a program correct on the
; strength of a decision the verifier made for its own convenience.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((mynil) (mycons (myhd Int) (mytl Lst)))))
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) (P (+ x 1)))))
(assert (forall ((x Int)) (=> (and (P x) (< x (myhd mynil))) false)))
(check-sat)
