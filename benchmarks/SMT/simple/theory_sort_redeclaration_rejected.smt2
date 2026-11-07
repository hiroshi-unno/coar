; Redeclares the theory sort Int.  Both z3 ("sort already defined") and cvc5
; ("previously declared as a type") reject this input; the tool refuses it
; with one error line and status 1, not with an uncaught exception.
(set-logic HORN)
(declare-sort Int 0)
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(check-sat)
