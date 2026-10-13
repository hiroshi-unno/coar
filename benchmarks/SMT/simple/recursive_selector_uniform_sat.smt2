; Positive control for non-uniform recursive selectors: uniform recursion retains Int selector results.
(declare-datatypes ((Tree 1)) ((par (T) ((leaf (value T)) (node (next (Tree T)))))))
(declare-const x0 (Tree Int))
(declare-const x1 (Tree Int))
(declare-const x2 (Tree Int))
(assert (distinct (value (next x0)) (value (next x1)) (value (next x2))))
(check-sat)
