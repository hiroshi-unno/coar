; **The false negative that the ghost parameters exist to avoid** -- POPL 2024's `state`, typed
; without any context information.  This is the first file of a triple; read it together with
;   arm_state_ghost_chc_sat.smt2    the same program with the ghost parameter (POPL 2024's fix)
;   arm_state_pred_poly_inst_sat.smt2 / arm_state_pred_poly_sat.smt2   with predicate polymorphism
; The program is typable; only the first encoding says otherwise.
;
;   state init (fun () -> let rec counter c = let i = perform Lookup in
;                         if i = 0 then c else (perform (Update (i-1)); counter (c+1))
;                         in counter 0)          assert  main : {init >= 0} -> {z | z = init}
;
; Without an abstracted predicate the handler must be typed against **one** answer refinement
; `A(z, s)` shared by every call of the operation.  Update's clause
;     fun _s -> continue k () x   :  (s:int) -> {z | A(z, x)}
; then has to meet the same `A` at the *outer* state, which forces `A(z,x) => A(z,s)` for all
; `s` -- i.e. the answer refinement cannot mention the state at all.  The program's answer *is*
; the state (`counter` returns `init`), so the specification becomes unprovable and the system
; is refuted.  This is exactly the "should be typable but comes out unsat" that the `(*ctx*)`
; arguments of benchmarks/OCaml/popl24/arm/state-SAT.ml were added to repair; measured on the
; program itself, RCaml gives `unsat,13` on the ghost-free source and `sat,18` with the ghosts.
;
; Plain CHC: no `declare-forall-fun` occurs, which is the syntactic signature of a context-free
; encoding.  expected: unsat
(set-logic HORN)
(declare-fun A (Int Int) Bool)

; the single answer refinement must survive Update's state change
(assert (forall ((x Int) (s Int) (z Int)) (=> (and (A z x) (not (A z s))) false)))
; the program answers `init` from the initial state `init`
(assert (forall ((s Int)) (=> (>= s 0) (A s s))))
; the specification: at initial state s the answer is s
(assert (forall ((s Int) (z Int)) (=> (and (>= s 0) (A z s) (not (= z s))) false)))
(check-sat)
