; Expected: unsat.  A solution must satisfy the constraints whatever the background theory left
; open, and the theory does not fix (tl nil): in the model where (tl nil) = nil the premise holds
; and `false` is demanded, so the constraint is not valid and no solution exists.
;
; This file also pins the other side of the question.  Deciding it instead by "is there SOME model
; of the theory satisfying the universal closure" answers sat -- that is plain SMT-LIB
; satisfiability, which is what Z3 answers as an SMT solver on the assertions of this file once
; the set-logic line is removed and the datatype renamed away from its predefined List/nil/hd/tl,
; and it is not the reading this tool uses.  Z3's Horn engine on the file as it stands answers
; unknown, so it takes no position:
; a candidate solution is accepted here only when every clause is VALID, so the two must agree.
; The tool answered sat between 2026-09-05 and 2026-09-12, when the two halves disagreed.
(set-logic HORN)
(declare-datatypes ((List 0)) (((nil) (cons (hd Int) (tl List)))))
(assert (forall ((x Int)) (=> (= (tl nil) nil) false)))
(check-sat)
