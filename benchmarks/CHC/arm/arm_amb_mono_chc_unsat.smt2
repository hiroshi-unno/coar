; The false negative for POPL 2024's `amb-3-simpl`.  Triple: this file (no context information,
; unsat), arm_amb_ghost_chc_sat.smt2 (the context supplied as parameters, sat) and
; arm_amb_pred_poly_sat.smt2 (predicate polymorphism, sat).
;
; In the evaluated source `select_from` is defined *inside* the closure handed to `amb`, where
; RCaml's let-generalization can give it a predicate-polymorphic type; the ghost-free version
; defines it at top level and RCaml answers `unsat,36`.  The reason, rendered here: a top-level
; `select_from` gets one answer refinement `A(z)` for all of its uses -- the outer call and every
; recursive one -- so `A` must hold both of the answer on the empty list (`false`) and of the
; answer when the element is found (`true`), and the specification "the answer is true" is
; refuted.  expected: unsat
(set-logic HORN)
(declare-fun A (Bool) Bool)
; the recursion: the empty list answers false, a found element answers true
(assert (A false))
(assert (A true))
; the handler transports the refinement unchanged, so the program's answer satisfies A
(assert (forall ((z Bool)) (=> (A z) (A z))))
; the specification of `test`: the answer is true
(assert (forall ((z Bool)) (=> (and (A z) (not z)) false)))
(check-sat)
