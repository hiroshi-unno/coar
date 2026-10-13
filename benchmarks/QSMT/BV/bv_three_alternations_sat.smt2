; Three quantifier alternations, so the solver must backtrack across levels
; rather than project once: with y = 63 (all ones) the inner disjunct z <=u y
; holds for every z.  Exercises the comparison rule at more than one level.
(set-logic BV)
(assert (forall ((x (_ BitVec 6))) (exists ((y (_ BitVec 6))) (forall ((z (_ BitVec 6))) (or (bvule z y) (bvule (bvadd x z) y))))))
(check-sat)
