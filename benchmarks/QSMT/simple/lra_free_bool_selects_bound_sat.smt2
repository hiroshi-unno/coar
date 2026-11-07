; A free Boolean constant chosen at the outermost level of a quantified LRA formula: satisfiable,
; with b true and x at most 1/2 (with b false, y = x falsifies y > x).  A solver whose strategy
; game has no Boolean sort must still read b, as an outermost existential.
(set-logic LRA)
(declare-fun b () Bool)
(declare-fun x () Real)
(assert (forall ((y Real))
  (and (=> b (or (>= y x) (< y 0.5)))
       (=> (not b) (> y x)))))
(check-sat)
