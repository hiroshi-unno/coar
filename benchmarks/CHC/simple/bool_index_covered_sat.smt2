; The acceptance test for the finite-index half of the array-equality finding.
; array-equality finding.  The index sort is finite and every one of its elements
; is stored, so the two arrays agree at every index a select can reach and their
; defaults are unobservable.  Comparing those defaults anyway is what makes this
; answer backwards.  z3 and cvc5 both give the verdict this file's name states.
; The rewrite in the simplifier now requires room in the index sort; what still
; compares the defaults is the value-level comparison, which is handed a dummy
; index VALUE rather than the index sort and so cannot tell a covered finite
; sort from an uncovered one.
(set-logic HORN)
(assert (= ((as const (Array Bool Int)) 0)
           (store (store ((as const (Array Bool Int)) 1) false 0) true 0)))
(check-sat)
