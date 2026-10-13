; A predicate whose defining clauses have exclusive and exhaustive guards but
; describe no total function: r(x, 0) at x = 0, r(x, y + 1) from r(x + 1, y)
; elsewhere.  Its least solution holds only for x <= 0, so the goal r(5, y)
; never fires and the problem is sat (r(x, y) := x <= 0).  Read as the
; "definition" f(x) = ite(x = 0, 0, f(x + 1) + 1) -- which does not terminate
; for x > 0 -- and replaced by y = f(5), the goal would claim no value equals
; f(5), which is unsat: a function reconstruction must refuse it for want of
; a totality proof.  Expected: sat.
(set-logic HORN)
(declare-fun r (Int Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (r x 0))))
(assert (forall ((x Int) (y Int))
  (=> (and (not (= x 0)) (r (+ x 1) y)) (r x (+ y 1)))))
(assert (forall ((y Int)) (=> (r 5 y) false)))
(check-sat)
