; Expected: sat,1.  The control for its parametric sibling: the same nullary unknown in the same
; place, without the `distinct` premise that makes the example parametric.  No witness question
; is asked here, so nothing converts a condition against the parameter environment, and the file
; answers.  The pair is what says the parametric path is the trigger rather than the nullary
; declaration on its own.
(set-logic DQHORN)
(declare-forall-sort a)
(declare-fun u () Int)
(declare-fun P (a Int) Bool)
(assert (forall ((x a)) (=> (= u 0) (P x 0))))
(assert (forall ((x a)) (=> (P x 0) false)))
(check-sat)
