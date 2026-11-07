; The satisfiable twin of arm_queue_dq_handoff_unsat.smt2: the same two-component handoff with
; **incomparable dependency sets** -- `Store` observes only the enqueueing context's refinement
; `XA`, `Resume` only the dequeueing context's `XB` -- made sound by the agreement the real
; program supplies at the handoff, `XA(z) => XB(z)`.
;
; In POPL 2024's `queue-1` that agreement is what the client's own typing establishes: the value
; enqueued by `Add_to_queue 42` is the one `Get_next` returns, so the dequeueing context's
; expectation is implied by the enqueueing context's guarantee.  Written as a premise at the
; clause's own variable, like a trait law (a premise on a universal function), it keeps the clause
; universal; a universal-predicate literal in a body is unrestricted in QECHC.
;
; `Store(z) := XA(z)` and `Resume(z) := XB(z)` is a solution, and neither unknown mentions the
; other's predicate -- which is the point: this is a Henkin structure, not a linear prefix.
; expected: sat
(set-logic DQHORN)
(declare-forall-fun XA (Int) Bool)
(declare-forall-fun XB (Int) Bool)
(declare-dep-exists-fun Store (XA) (Int) Bool)
(declare-dep-exists-fun Resume (XB) (Int) Bool)

; (1) the producer stores what its context guarantees
(assert (forall ((z Int)) (=> (XA z) (Store z))))
; (2) the handoff, under the agreement the client establishes
(assert (forall ((z Int)) (=> (and (=> (XA z) (XB z)) (Store z)) (Resume z))))
; (3) the consumer meets its own context's expectation
(assert (forall ((z Int)) (=> (and (Resume z) (not (XB z))) false)))
(check-sat)
