; The false negative for POPL 2024's `yield`, whose context information lives in the `[@@@rtype]`
; annotations `p0`..`p3` of the `Susp` and `Result` constructors.  Triple: this file,
; arm_yield_ghost_chc_sat.smt2, arm_yield_pred_poly_sat.smt2.
;
; Without those annotations the iterator's contract is one predicate `A(r)` on the values a leaf
; may hold, shared by the tree before and after the walk.  The program turns 0s into 1s, so `A`
; must accept both, and the specification "the result's leaves are 1" is refuted.  expected: unsat
(set-logic HORN)
(declare-fun A (Int) Bool)
(assert (A 0))     ; the input tree's leaves
(assert (A 1))     ; the output tree's leaves
(assert (forall ((r Int)) (=> (and (A r) (not (= r 1))) false)))
(check-sat)
