; The POPL 2024 ARM benchmark `state-SAT.ml` with its **ghost parameters removed**, encoded as
; QCHC, CHC over universally quantified predicate symbols (declare-forall-fun).
;
; Kawamata, Unno, Sekiyama, Terauchi, "Answer refinement modification", PACMPL 8 (POPL 2024),
; section 4.2: the formal system gives the state handler's operations predicate-polymorphic types
;   Update : forall X:(int,int). (x:int) -> (unit -> ((s:int) -> {z | X(z,s)}))
;                                        -> ((s:int) -> {z | X(z,x)})
; and Lookup the analogue in which the continuation may assume that the value it receives is the
; current state.  The implementation infers predicate-polymorphic types only at let-bindings, so
; the experiments passed the client's local counter `c` to Lookup and Update as a **ghost
; parameter** (benchmarks/OCaml/popl24/arm/state-SAT.ml, the `(*ctx*)` arguments) and annotated
; the clauses with the concrete answer refinements `z = ctx + s`, `z = ctx2 + 1 + s'`.  The
; ghost-free program is benchmarks/OCaml/safety/alg_eff/obsolete/ARM_bench/eff/unused/
; state-noctx-SAT.ml, which that implementation cannot verify: "completely inferring predicate
; variables requires higher-order predicate constraints, which are not expressible with CHC"
; (section 6).  They are expressible here: X is a universal predicate symbol and the client's
; unknowns depend on it.
;
; The program:
;   state init (fun () -> let rec counter c = let i = perform Lookup in
;                         if i = 0 then c else (perform (Update (i-1)); counter (c+1))
;                         in counter 0)
;   assert  main : (init:{z | z >= 0}) -> {z | z = init}
;
; Two halves:
;  (1) the handler is verified ONCE for every X (the generalization side);
;  (2) the client instantiates X at an *inferred* predicate -- the spec of the rest of the
;      computation, which mentions the local `c`.  That is what the ghost parameter faked.
;      Instantiation is encoded by quantifying over X and equating it with the client's
;      unknown by a universally quantified premise.
; The specification is wrong here -- `z = init + 1` instead of `z = init` -- so the same
; constraint system must be refuted.  expected: unsat
(set-logic DQHORN)

; the abstracted answer refinement X(z,s): result z when the continuation is resumed at state s
(declare-forall-fun X (Int Int) Bool)

; --- (1) the handler, verified once for every X ---------------------------------------------
; Lookup clause   fun s -> continue k s s : (s:int) -> {z | X(z,s)}
;   continuation k : (v:int) -> (s:{s | s = v}) -> {z | X(z,s)}
(declare-dep-exists-fun HLook (X) (Int Int) Bool)
(assert (forall ((s Int) (z Int)) (=> (X z s) (HLook s z))))
(assert (forall ((s Int) (z Int)) (=> (and (HLook s z) (not (X z s))) false)))
; Update clause   fun _s -> continue k () x : (s:int) -> {z | X(z,x)}
(declare-dep-exists-fun HUpd (X) (Int Int Int) Bool)
(assert (forall ((x Int) (s Int) (z Int)) (=> (X z x) (HUpd x s z))))
(assert (forall ((x Int) (s Int) (z Int)) (=> (and (HUpd x s z) (not (X z x))) false)))

; --- (2) the client, ghost-free ---------------------------------------------------------------
; Cnt(c,s,z): running `counter c` with the handler at state s yields z
; Cnt does NOT depend on X: it is the client's own spec, and the default dependency set
; ("every earlier Bool forall-fun") would let a solution read the abstracted predicate
(declare-dep-exists-fun Cnt () (Int Int Int) Bool)
; i = perform Lookup, i = 0: the computation returns c at the unchanged state
(assert (forall ((c Int) (s Int)) (=> (= s 0) (Cnt c s c))))
; i <> 0: perform (Update (i-1)) then counter (c+1); the Update contract is used at
; X := (z,s') |-> Cnt(c+1,s',z), the spec of the rest -- the instantiation the ghost parameter
; stood in for
(assert (forall ((c Int) (s Int) (z Int))
  (=> (and (not (= s 0))
           (forall ((z2 Int) (s2 Int)) (= (X z2 s2) (Cnt (+ c 1) s2 z2)))
           (HUpd (- s 1) s z))
      (Cnt c s z))))
; the (wrong) specification of main: state init (counter 0) = init + 1
(assert (forall ((init Int) (z Int))
  (=> (and (>= init 0) (Cnt 0 init z) (not (= z (+ init 1)))) false)))
(check-sat)
