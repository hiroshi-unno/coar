; Satisfiable.  A functional predicate P(x, b) with a Boolean result and one
; clause
;   P(x, b) => (b or x > 0)
; For x > 0 both Booleans fit; elsewhere only true.  A solution:
; P(x, b) := (b = true).  Two witnesses must not make the answer unsat (the
; predicate need only pick one).  Was a timeout under both preprocessing
; settings: the Boolean result kept it out of the strategy game.  Expected: sat.
(set-logic HORN)
(declare-fnp P (Int Bool) Bool)
(assert (forall ((x Int) (b Bool)) (=> (P x b) (or b (> x 0)))))
(check-sat)
