; The decrease is on the real coordinate (r >= 1, r' = r - 1) and the integer
; one is unconstrained.  Template configs answer sat (ranking r); the decision-tree classifier ranks
; integer coordinates only and must report 'no halfspace separates ... over its integer coordinates'
; instead of crashing.  Expected: sat (or that error under pcsat_dt*.json).
(set-logic HORN)
(declare-wfp WF (Int Real Int Real) Bool)
(assert (forall ((x Int) (r Real) (x1 Int) (r1 Real))
  (=> (and (>= r 1.0) (= r1 (- r 1.0))) (WF x r x1 r1))))
(check-sat)
