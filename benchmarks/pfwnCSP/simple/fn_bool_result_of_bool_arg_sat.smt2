; Satisfiable.  A functional predicate P(a, r) with a Boolean argument and a
; Boolean result, whose clauses are
;   P(a, r) => (r = not a)        P(a, r) => (r or a)
; A solution: P(a, r) := (r = not a), total and single-valued.
;
; What the file is for: the strategy game that eliminates a functional
; predicate before the CEGIS loop reads linear arithmetic only, so a Boolean
; result (or argument) was never eliminated there, and the loop's template for
; a Boolean function of Boolean arguments has no candidate result.  Such a
; predicate is now decided by one validity question,
; forall a. body(a, true) \/ body(a, false).  Expected: sat.
(set-logic HORN)
(declare-fnp P (Bool Bool) Bool)
(assert (forall ((a Bool) (r Bool)) (=> (P a r) (= r (not a)))))
(assert (forall ((a Bool) (r Bool)) (=> (P a r) (or r a))))
(check-sat)
