; POPL 2024's repair for `select`: the ghost parameter carries the client's `x` into the handler,
; so the refinement is indexed by it -- `A(x, ok, h)`.  Middle file of the triple.  expected: sat
(set-logic HORN)
(declare-fun A (Int Bool Int) Bool)
(assert (forall ((x Int)) (A x true x)))          ; the first successful choice is x
(assert (forall ((x Int) (ok Bool) (h Int)) (=> (and (A x ok h) (not (and ok (= h x)))) false)))
(check-sat)
