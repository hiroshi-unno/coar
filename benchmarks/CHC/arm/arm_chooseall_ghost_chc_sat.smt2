; POPL 2024's repair for `choose-all`: the refinement is indexed by the call site, so the inner
; and the outer `Decide` are described separately.  Middle file of the triple.  Lists are
; abstracted to their length.  expected: sat
(set-logic HORN)
(declare-fun A (Int Bool Int) Bool)
(declare-fun Ans (Int Int) Bool)
(assert (forall ((c Int) (n1 Int) (n2 Int))
  (=> (and (A c true n1) (A c false n2)) (Ans c (+ n1 n2)))))
(assert (A 1 true 1))   (assert (A 1 false 1))    ; the inner call answers singletons
(assert (A 2 true 2))   (assert (A 2 false 2))    ; the outer call answers pairs
(assert (forall ((n Int)) (=> (and (Ans 2 n) (not (= n 4))) false)))
(check-sat)
