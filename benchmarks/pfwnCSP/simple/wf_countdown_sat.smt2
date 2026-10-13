; The countdown loop  while (x > 0) x--  as a well-foundedness problem: R must contain the
; loop's step and be well-founded.  Over the intended structure Z this is SATISFIABLE (R := the
; step itself, ranking x), which is how the tool answers it.  Read in every model of Th(Z) it
; would not be: a non-standard N gives N, N-1, ... an infinite descending chain
; (a bounded-termination argument over first-order models).  Predicate kinds are read over the
; intended structure, so the expected verdict is sat.  expected: sat
(set-logic HORN)
(declare-wfp R (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (> x 0) (= y (- x 1))) (R x y))))
(check-sat)
