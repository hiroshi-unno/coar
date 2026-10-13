; expected: sat
;
; The direction the repair must not overshoot into: with no repetition,
; `(distinct x y z)` is the conjunction of the three disequalities and is
; satisfiable, so this clause's premise is satisfiable and the verdict is `sat`
; -- a repair that made every `distinct` false, or that generated pairs for
; positions it should not, would show up here.
(set-logic HORN)
(declare-fun P (Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (distinct x y z) (P x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (P x y z) (= x y)) false)))
(check-sat)
