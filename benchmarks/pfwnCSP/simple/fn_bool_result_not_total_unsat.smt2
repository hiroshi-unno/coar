; Unsatisfiable.  A functional predicate P(x, b) with a Boolean result and one
; clause
;   P(x, b) => (x > 0 and b)
; At x <= 0 no b fits, so P cannot be total.  With preprocessing on this was
; already unsat; with it off (pcsat_wopp_tbq_ar) it was a timeout, the Boolean
; result keeping it out of the strategy game.  Expected: unsat.
(set-logic HORN)
(declare-fnp P (Int Bool) Bool)
(assert (forall ((x Int) (b Bool)) (=> (P x b) (and (> x 0) b))))
(check-sat)
