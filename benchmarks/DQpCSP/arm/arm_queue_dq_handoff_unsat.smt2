; **A genuinely dependency-quantified instance out of the ARM corpus**,
; and the first one in this corpus: two unknowns whose dependency sets are *incomparable*.
;
; Where it comes from.  In POPL 2024's `queue-1`, `Add_to_queue` stores a continuation and a
; later `Get_next` resumes it.  The two sites are in different contexts, so each has its own
; abstracted answer refinement: `XA` for the enqueueing context, `XB` for the dequeueing one.
; The producer side of the handler can only know what the *enqueueing* context guarantees, and
; the consumer side only what the *dequeueing* context expects -- neither observes the other's
; predicate.  That is a dependency structure, not a prefix:
;
;     Store  depends on {XA}      Resume depends on {XB}
;
; and the queue is the medium that hands a value from one to the other.  With nothing relating
; the two contexts the handoff is unsound, and this file measures that: the value the producer
; guarantees under `XA` reaches a consumer that demands `XB`, so satisfiability would need
; `XA(z) => XB(z)` for **every** pair of interpretations, which fails at `XA = true`, `XB = false`.
;
; Note that *enlarging* a dependency set does not rescue it: letting `Store` also observe
; `XB` does not help, because clause (1) still forces `Store` to hold wherever `XA` does.  What
; rescues it is the premise the real program supplies -- see arm_queue_dq_handoff_sat.smt2.
; expected: unsat
(set-logic DQHORN)
(declare-forall-fun XA (Int) Bool)      ; the enqueueing context's answer refinement
(declare-forall-fun XB (Int) Bool)      ; the dequeueing context's
(declare-dep-exists-fun Store (XA) (Int) Bool)
(declare-dep-exists-fun Resume (XB) (Int) Bool)

; (1) Add_to_queue: the producer stores what its own context guarantees
(assert (forall ((z Int)) (=> (XA z) (Store z))))
; (2) the handoff through the queue: what was stored is what is resumed
(assert (forall ((z Int)) (=> (Store z) (Resume z))))
; (3) Get_next: the consumer must meet its own context's expectation
(assert (forall ((z Int)) (=> (and (Resume z) (not (XB z))) false)))
(check-sat)
