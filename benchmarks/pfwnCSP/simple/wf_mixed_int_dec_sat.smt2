; A WF predicate with an integer and a real argument whose decrease
; is on the integer.  The decision-tree classifier (pcsat_dt.json) ranks the integer coordinate and
; answers sat; the template configs (pcsat_tbq_ar.json) answer sat as well.  Expected: sat.
(set-logic HORN)
(declare-wfp WF (Int Real Int Real) Bool)
(assert (forall ((x Int) (r Real) (x1 Int) (r1 Real))
  (=> (and (> x 0) (= x1 (- x 1)) (= r1 (/ r 2.0))) (WF x r x1 r1))))
(check-sat)
