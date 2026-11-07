; A quantified formula that simplifies to the constant false: unsatisfiable.  The body is a
; disjunction of comparisons each of which is false for every value (t - t < 0), the shape a
; weak-simulation formula takes when one step cannot be matched.  After simplification no
; arithmetic is left, and a solver that classifies its input by theory must still answer it.
(set-logic LIA)
(assert (forall ((x Int) (y Int)) (or (< (+ x (- x)) 0) (< (- (+ y (- y))) 0))))
(check-sat)
