; Satisfiable.  A functional predicate P over the Booleans with one clause
;   P(b) => b
; A solution: P(b) := (b = true).
;
; What the file is for: the strategy game that eliminates a functional
; predicate before the CEGIS loop reads linear arithmetic only and declined
; the Boolean witness, and the loop's template for a Boolean constant has no
; candidate result (it draws its candidates from qualifiers over the
; arguments, and there are none), so this was a timeout under both
; preprocessing settings.  Expected: sat.
(set-logic HORN)
(declare-fnp P (Bool) Bool)
(assert (forall ((b Bool)) (=> (P b) b)))
(check-sat)
