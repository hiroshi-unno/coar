; Expected: sat,5.  Kept as the input that REACHES the parametric hole-map builder with a nullary
; unknown in the problem -- 138 calls to it under tracing -- and does not fail there.
;
; Two things had to be true at once and each cost an attempt.  The predicate must SURVIVE
; preprocessing, or there is no predicate application left to be parametric about: defined by one
; rule and one goal it is removed by the predicate eliminator, and what reaches synthesis is the
; pure constraint left behind, which goes to the other arm entirely.  Making it recursive -- the
; middle clause feeding itself -- is what keeps it.  And the example must be parametric, which the
; `distinct` premise over the quantified sort does.
;
; What it shows: an unknown reaches the parametric arm through an example atom's ARGUMENTS, which
; by then carry clause variables and model values, so the nullary case that breaks the other arm
; does not arise here.  The unknown survives symbolically in a CONDITION instead, and a condition
; is what the other arm and the witness question read -- which is why those two failed and this one
; does not.
(set-logic DQHORN)
(declare-forall-sort a)
(declare-fun u () Int)
(declare-fun P (a Int) Bool)
(assert (forall ((x a)) (=> (= u 0) (P x 0))))
(assert (forall ((x a) (n Int)) (=> (P x n) (P x (+ n 1)))))
(assert (forall ((x a) (y a) (n Int)) (=> (and (distinct x y) (P x n) (> n 5)) false)))
(check-sat)
