; b must be true, and false whenever x > 0: infeasible.
(set-logic LIA)
(synth-fun b () Bool)
(declare-var x Int)
(constraint b)
(constraint (=> (> x 0) (not b)))
(check-synth)
