; POPL 2024's repair for `bfs-simpl`: the ghost parameter carries the client's `a` into the
; handler, so the refinement of a queued resumption is indexed by it -- `A(a, ok, v)`.  Middle
; file of the triple.  expected: sat
(set-logic HORN)
(declare-fun A (Int Bool Int) Bool)
(assert (forall ((a Int)) (A a true a)))
(assert (forall ((a Int)) (A a true (- 0 a))))
(assert (forall ((a Int) (ok Bool) (v Int))
  (=> (and (A a ok v) (not (and ok (= (* v v) (* a a))))) false)))
(check-sat)
