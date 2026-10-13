; A disjunctively well-founded predicate is one contained in a finite union of
; well-founded relations (Podelski and Rybalchenko).  D must contain the
; two-cycle {(0,1), (1,0)}, which is the union of the well-founded relations
; {(0,1)} and {(1,0)}, so D := (x = 0 /\ y = 1) \/ (x = 1 /\ y = 0) is a
; solution and the problem is satisfiable.  A sample refutes DWF only by a
; self-loop; a learner that refutes every cycle, as it may for WF, answers
; unsat here.
(set-logic HORN)
(declare-dwfp D (Int Int) Bool)
(assert (D 0 1))
(assert (D 1 0))
(check-sat)
