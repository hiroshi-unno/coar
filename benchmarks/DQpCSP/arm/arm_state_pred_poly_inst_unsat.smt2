; The POPL 2024 ARM state handler with predicate-polymorphic operation signatures, verified once
; for every X, and a client that instantiates X explicitly (predicate polymorphism
; encoded by universally quantified predicates).  Companion of arm_state_pred_poly_sat.smt2, whose client is the
; recursive `counter` and whose instantiation is inferred.
;
; Kawamata, Unno, Sekiyama, Terauchi, PACMPL 8 (POPL 2024), section 4.2:
;   Update : forall X:(int,int). (x:int) -> (unit -> ((s:int) -> {z | X(z,s)}))
;                                        -> ((s:int) -> {z | X(z,x)})
;   Lookup : forall X:(int,int). (unit)  -> ((v:int) -> (s:{s | s = v}) -> {z | X(z,s)})
;                                        -> ((s:int) -> {z | X(z,s)})
; Their implementation cannot give operations predicate-polymorphic types and passes the client's
; local variable as a ghost parameter instead (benchmarks/OCaml/popl24/arm/state-SAT.ml).  Here
; the two clauses are checked against the polymorphic signatures directly, for a universally
; quantified X, and the client supplies the instantiation as a curried lambda array.
;
; Client:  state init (fun () -> perform (Update 5); perform Lookup)   wrong spec: result = 6.
; The continuation of Update is `perform Lookup`, of type (s:int) -> {z | z = s}, so X is
; instantiated at (z,s) |-> z = s and Update's result type gives {z | X(z,5)} = {z | z = 5}.
; The specification is wrong here (result = 6 instead of 5), so the system must be refuted.
; expected: unsat
(set-logic DQHORN)

(declare-forall-fun X (Int Int) Bool)
; the handler clause specs carry the abstracted predicate as an explicit array argument, so that
; a client can instantiate it (the front end prepends declared dependencies and has no syntax for
; instantiating one)
(declare-dep-exists-fun HLook () ((Array Int (Array Int Bool)) Int Int) Bool)
(declare-dep-exists-fun HUpd () ((Array Int (Array Int Bool)) Int Int Int) Bool)

; --- the handler, verified once for every X ---
; Lookup:  fun s -> continue k s s   with k : (v:int) -> (s:{s = v}) -> {z | X(z,s)}
(assert (forall ((s Int) (z Int)) (=> (X z s) (HLook X s z))))
(assert (forall ((s Int) (z Int)) (=> (and (HLook X s z) (not (X z s))) false)))
; Update:  fun _s -> continue k () x  with k : (unit) -> (s:int) -> {z | X(z,s)}
(assert (forall ((x Int) (s Int) (z Int)) (=> (X z x) (HUpd X x s z))))
(assert (forall ((x Int) (s Int) (z Int)) (=> (and (HUpd X x s z) (not (X z x))) false)))

; --- the client: X := (z,s) |-> z = s, the spec of the continuation `perform Lookup` ---
(assert (forall ((init Int) (z Int))
  (=> (and (HUpd (lambda ((z2 Int)) (lambda ((s2 Int)) (= z2 s2))) 5 init z) (not (= z 6)))
      false)))
(check-sat)
