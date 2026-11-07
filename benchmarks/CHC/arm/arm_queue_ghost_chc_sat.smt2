; POPL 2024's repair for `queue-1`: the operation takes a **context label** it never uses, so the
; one answer refinement may be indexed by it -- `A(ctx, z, q)` -- and the two `Get_next` calls of
; the client pass `1` and `2`.  Nothing collapses any more, because the obligation of
; `Add_to_queue`'s clause now relates the same label to itself.  Middle file of the triple; see
; arm_queue_mono_chc_unsat.smt2 for the false negative it repairs and arm_queue_pred_poly_sat.smt2
; for the same thing done by abstracting the predicate instead of labelling the call.
;
; The label is a first-order value, so this stays plain CHC -- and it is satisfiable, e.g.
; `A(ctx, z, q) := (ctx = 1 => (z <=> q != []))  /\  (ctx = 2 => not z)`.  expected: sat
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-fun A (Int Bool Lst) Bool)

; Add_to_queue's clause, at a fixed context label
(assert (forall ((c Int) (y Int) (z Bool)) (=> (A c z (cons y nil)) (A c z (cons y nil)))))
; call 1 (label 1): from the queue [42] the first Get_next answers Some
(assert (A 1 true (cons 42 nil)))
; call 2 (label 2): from the empty queue the second Get_next answers None
(assert (A 2 false nil))
; the specification, at the label of the call that produces the program's answer
(assert (forall ((z Bool)) (=> (and (A 2 z nil) z) false)))
(check-sat)
