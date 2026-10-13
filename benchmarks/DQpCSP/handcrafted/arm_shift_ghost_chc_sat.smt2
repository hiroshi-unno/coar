; POPL 2024's repair for `shift`: the ghost parameter labels the delimited context, so the
; continuation's refinement is indexed by it -- `K(ctx, s, z)`.  Middle file of the triple.
; expected: sat
(set-logic HORN)
(declare-fun K (Int Int Int) Bool)
(assert (forall ((s Int)) (K 1 s (+ (* 2 s) 1))))
(assert (forall ((s Int)) (K 2 s (+ s 5))))
(assert (forall ((n Int) (z1 Int) (z2 Int) (z3 Int))
  (=> (and (K 1 n z1) (K 1 z1 z2) (K 1 z2 z3) (not (= z3 (+ (* 8 n) 7)))) false)))
(check-sat)
