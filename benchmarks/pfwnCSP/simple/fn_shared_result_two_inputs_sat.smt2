; One variable is the result of a functional unknown at two different inputs: the goal needs f(0) = f(x) for some
; x >= 1 with p(0), and f(0) = 0, f(x) = 1 otherwise, p := true, is a solution (sat).  Reading the shared result
; as one value that the function's totality supplies at once refutes it.
(set-logic HORN)
(declare-fun p (Int) Bool)
(declare-fnp f (Int Int) Bool)
(assert (p 0))
(assert (forall ((x Int) (y Int)) (=> (and (p 0) (f 0 y) (f x y) (>= x 1)) false)))
(check-sat)
