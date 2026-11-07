; The false negative for POPL 2024's `deferred`, where the ghost information is carried by a
; **constructor field** rather than an operation argument.  Triple:
;   arm_deferred_mono_chc_unsat.smt2  no context information           -> unsat  (this file)
;   arm_deferred_ghost_chc_sat.smt2   the ctxinfo field of `Thunk`     -> sat    (POPL 2024's fix)
;   arm_deferred_pred_poly_sat.smt2   predicate polymorphism           -> sat    (ours, QCHC)
;
; The evaluated source declares
;   type deferred = Value of int | Thunk of int(*ctxinfo*) * (unit -> int)
;   [@@@rtype "Thunk :: (c: {z | p3(z)}) -> (f: unit -> {z | p4(z, c)}) -> ..."]
; and the ghost-free version drops the `int` field.  Without it the thunk's postcondition is one
; predicate `A(z)` fixed for every use of the datatype, so it cannot mention the client's `n` --
; and `test n = lazy_ (fun () -> n) (fun () -> perform Force)` must be typed for **every** `n`.
; `A` therefore has to accept every value, the answer becomes unconstrained, and the
; specification `z = n` is refuted.  RCaml agrees on the program itself: `unsat,0` ghost-free,
; `sat,0` with the field.  expected: unsat
(set-logic HORN)
(declare-fun A (Int) Bool)      ; the one postcondition every thunk gets
(declare-fun Ans (Int) Bool)    ; the answer of `test`

; Force: the thunk's value satisfies A, and `test` returns it
(assert (forall ((z Int)) (=> (A z) (Ans z))))
; the thunk `fun () -> n` returns n, for every n the client may pass
(assert (forall ((n Int)) (A n)))
; the specification: for every n, `test n` answers n
(assert (forall ((n Int) (z Int)) (=> (and (Ans z) (not (= z n))) false)))
(check-sat)
