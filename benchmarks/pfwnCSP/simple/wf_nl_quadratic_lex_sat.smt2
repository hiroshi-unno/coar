; Well-founded: x := x + y, y := y - 1 while x > 0.  x may grow for a while (quadratically in y),
; but the lexicographic pair (max(y, -1), x) decreases: y decreases while y >= 0, and once y < 0
; x decreases.  Expected: sat.
(set-logic HORN)
(declare-wfp WF (Int Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int)) (=> (and (> x 0) (= x1 (+ x y)) (= y1 (- y 1))) (WF x y x1 y1))))
(check-sat)
