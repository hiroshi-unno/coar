; A definition body applies a Boolean function that nothing declares (the names
; of a re-emitted input drifted from its declarations).  z3 and cvc5 reject it as
; an unknown symbol; the reader refuses it in one line.
(set-logic HORN)
(declare-fun p (Int) Bool)
(define-fun inv ((x Int)) Bool (and (>= x 0) (q_undeclared x)))
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (p x) (inv x))))
(check-sat)
