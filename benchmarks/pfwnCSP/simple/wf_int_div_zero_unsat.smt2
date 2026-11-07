; NOT well-founded in every model: (div x 0) is unspecified by SMT-LIB, and in a model where it
; is x the relation has a self-loop.  Expected: unsat (or unknown), never sat.
(set-logic HORN)
(declare-wfp WF (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (> x 0) (= y (div x 0))) (WF x y))))
(check-sat)
