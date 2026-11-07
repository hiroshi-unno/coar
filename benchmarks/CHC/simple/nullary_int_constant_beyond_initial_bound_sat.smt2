; Expected: sat (u = 37).
;
; A nullary integer function unknown whose only solution lies far outside the template's initial
; constant bound, so PCSat's integer function template must grow many times before it can
; propose it.  It is the input on which the growth rule of a nullary Int unknown is visible: the
; template-state dump of a dbg_ run (number of cases, constant bound) records every growth step,
; and a change to that rule shows up as a different sequence while the verdict stays sat.
(set-logic HORN)
(declare-fun u () Int)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) (= (+ x u) 37))))
(check-sat)
