; The false negative for POPL 2024's `queue-1`, and the clearest one in the corpus: there the
; ghost parameter is a bare **context label**.  The source calls the same operation twice,
; `perform (Get_next 1(*dummy*))` and `perform (Get_next 2(*dummy*))`, with an argument the
; handler never reads -- its only purpose is to let the two calls have different answer
; refinements.  Triple:
;   arm_queue_mono_chc_unsat.smt2   no context information  -> unsat  (this file)
;   arm_queue_ghost_chc_sat.smt2    the ghost label 1 / 2   -> sat    (POPL 2024's fix)
;   arm_queue_pred_poly_sat.smt2    predicate polymorphism  -> sat    (ours, QCHC)
;
;   queue initial body = ... { Get_next _ctx  -> fun k -> fun q -> ...
;                              Add_to_queue y -> fun k -> fun q -> continue k () (q @ [y]) }
;   let main init = queue init (fun () -> perform (Add_to_queue 42);
;                                         let _ = perform (Get_next 1) in perform (Get_next 2))
;   assert  main : {z: int list | z = []} -> {z: int option | z = None}
;
; With one answer refinement `A(z, q)` for every call, `Add_to_queue`'s clause
;     fun q -> continue k () (q @ [y])   :  (q:list) -> {z | A(z, q)}
; must meet `A` at the *outer* queue while the continuation has it at `q @ [y]`, so
; `A(z, q @ [y]) => A(z, q)`: what holds after an enqueue must already hold before it.  The
; program answers `Some 42` from the queue `[42]` and must answer `None` from the empty queue,
; and those two are now the same demand.  Refuted.
;
; `int option` is abstracted to its `is_Some` bit.  Plain CHC, no `declare-forall-fun`.
; expected: unsat
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-fun A (Bool Lst) Bool)

; Add_to_queue's clause under a single answer refinement
(assert (forall ((y Int) (z Bool)) (=> (and (A z (cons y nil)) (not (A z nil))) false)))
; the program answers Some from the queue [42]
(assert (A true (cons 42 nil)))
; the specification: from the empty queue the answer is None
(assert (forall ((z Bool)) (=> (and (A z nil) z) false)))
(check-sat)
