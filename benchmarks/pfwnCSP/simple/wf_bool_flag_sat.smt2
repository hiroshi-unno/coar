; A WF predicate whose only decrease is a Bool flag going from true to
; false (the integer is unchanged).  The decision-tree classifier ranks the flag as 0/1
; (ite b 1 0) since 2026-09-06; before, Bool coordinates hit force_int's assert.  Expected: sat.
(set-logic HORN)
(declare-wfp WF (Bool Int Bool Int) Bool)
(assert (forall ((b Bool) (x Int) (b1 Bool) (x1 Int))
  (=> (and b (not b1) (= x1 x)) (WF b x b1 x1))))
(check-sat)
