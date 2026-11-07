; |x| and x are one variable, so the constraint says x <> x: infeasible.
(set-logic LIA)
(synth-fun |f| ((z Int)) Int)
(declare-var |x| Int)
(constraint (= (f x) 0))
(constraint (not (= |x| x)))
(check-synth)
