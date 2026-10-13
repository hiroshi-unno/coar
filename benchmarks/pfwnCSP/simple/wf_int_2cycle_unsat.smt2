; An integer WF predicate whose examples admit no ranking (a swap 2-cycle).
; The decision-tree classifier must reach unsat through its implicit-cycle cut; while the classifier
; returned every learned ranking as false, every dt configuration looped on it.  Expected: unsat.
(set-logic HORN)
(declare-wfp WF (Int Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (>= x 0) (>= y 0) (not (= x y)) (= x1 y) (= y1 x)) (WF x y x1 y1))))
(check-sat)
